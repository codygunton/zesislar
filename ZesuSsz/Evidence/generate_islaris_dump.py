#!/usr/bin/env python3
"""Generate an Islaris dump from a pinned objdump listing and a region profile."""

import argparse
import json
import re
from pathlib import Path

INSTRUCTION = re.compile(r"^\s*([0-9a-f]+):\s+[0-9a-f]+\s+(.+)$")
MEMORY_INSTRUCTION = re.compile(
    r"^(l(?:b|bu|h|hu|w|wu|d)|s[bdhw])\s+[^,]+,\s*(-?\d+)\(([^)]+)\)"
)
MEMORY_WIDTHS = {
    "lb": 1, "lbu": 1, "sb": 1,
    "lh": 2, "lhu": 2, "sh": 2,
    "lw": 4, "lwu": 4, "sw": 4,
    "ld": 8, "sd": 8,
}

RISCV_ABI_REGISTERS = {
    "zero": "x0", "ra": "x1", "sp": "x2", "gp": "x3", "tp": "x4",
    "t0": "x5", "t1": "x6", "t2": "x7", "s0": "x8", "fp": "x8",
    "s1": "x9", "a0": "x10", "a1": "x11", "a2": "x12", "a3": "x13",
    "a4": "x14", "a5": "x15", "a6": "x16", "a7": "x17", "s2": "x18",
    "s3": "x19", "s4": "x20", "s5": "x21", "s6": "x22", "s7": "x23",
    "s8": "x24", "s9": "x25", "s10": "x26", "s11": "x27", "t3": "x28",
    "t4": "x29", "t5": "x30", "t6": "x31",
}


def write_text_if_changed(path: Path, text: str) -> None:
    if path.exists() and path.read_text() == text:
        return
    path.write_text(text)


def load_store_spec_annotations(
    instruction: str, memory_bases: dict[str, str] | None = None,
    array_view: dict[str, object] | None = None,
) -> list[str]:
    match = MEMORY_INSTRUCTION.match(instruction)
    if match is None or match.group(1) not in {"ld", "lbu", "sd"}:
        return []
    opcode, offset, base = match.groups()
    byte_array = array_view is not None and array_view.get("kind") == "byte"
    if opcode == "lbu" and (
            not byte_array or base != array_view["base"]):
        return []
    alignment = 1 if opcode == "lbu" else 8
    if int(offset) < 0 or int(offset) % alignment != 0:
        return []
    if memory_bases is not None and base not in memory_bases:
        return []
    operand = instruction.split(maxsplit=1)[1].split(",", 1)[0]
    if operand not in RISCV_ABI_REGISTERS or base not in RISCV_ABI_REGISTERS:
        return []
    # A load from an array view keeps its raw Isla trace: AGENTS.md
    # forbids a `//@spec:` for a load or store from an array.
    if (opcode in {"ld", "lbu"} and array_view is not None
            and base == array_view["base"]):
        return []
    spec = f"zesu_{opcode}_spec"
    if opcode == "ld" and operand == base and not byte_array:
        spec = "zesu_ld_same_spec"
        arguments = f'"{RISCV_ABI_REGISTERS[operand]}" ({offset})'
    else:
        arguments = (f'"{RISCV_ABI_REGISTERS[operand]}" '
                     f'"{RISCV_ABI_REGISTERS[base]}" ({offset})')
    tactic = "all: (try bv_solve; try lia)."
    return [
        "//@import: InstrSpecs.Specs",
        f"//@spec: {spec} pc {arguments}",
        f"//@spec_tactic: {tactic}",
    ]


def load_array_view(
    pc: int, profile: dict[str, object],
) -> dict[str, object] | None:
    return next((view for view in profile.get("loadArrayViews", [])
                 if int(view["start"], 0) <= pc < int(view["end"], 0)), None)


def jump_spec_annotations(
    instruction: str, jump_registers: dict[str, str],
) -> list[str]:
    match = INDIRECT_JUMP.match(instruction)
    if match is None or not instruction.startswith("jalr"):
        return []
    offset_text, base = match.groups()
    if base != "ra" or jump_registers.get(base) != "x1":
        return []
    encoded_offset = int(offset_text) % (1 << 64)
    return [
        "//@import: InstrSpecs.Specs",
        f'//@spec: zesu_jalr_same_spec pc "x1" (BV 64 {encoded_offset})',
        "//@spec_tactic: all: bv_solve.",
    ]


def configured_spec_annotations(
    pc: int, profile: dict[str, object],
) -> list[str]:
    """Return the reviewed spec annotation for one configured instruction."""
    configured = profile.get("instructionSpecs", {})
    spec = configured.get(f"0x{pc:x}")
    if spec is None:
        return []
    return [
        "//@import: InstrSpecs.Specs",
        f"//@spec: {spec['spec']}",
        f"//@spec_tactic: {spec['tactic']}",
    ]


def effective_address_constraints(instruction: str, bases: dict[str, str]) -> list[str]:
    match = MEMORY_INSTRUCTION.match(instruction)
    if match is None:
        return []
    opcode, offset_text, base = match.groups()
    register = bases.get(base)
    if register is None:
        return []
    width = MEMORY_WIDTHS[opcode]
    alignment_bits = width.bit_length() - 1
    offset = int(offset_text) % (1 << 64)
    address = f"(bvadd {register} 0x{offset:016x})"
    constraints = [
        f"bvuge {address} rv_ram_base",
        f"bvule {address} (bvsub (bvadd rv_ram_base rv_ram_size) "
        f"0x{width:016x})",
    ]
    if alignment_bits:
        constraints.insert(
            0,
            f"= ((_ extract {alignment_bits - 1} 0) {address}) "
            f"0b{'0' * alignment_bits}",
        )
    return constraints


BRANCHES = {"beq", "bne", "blt", "bge", "bltu", "bgeu", "beqz", "bnez", "j"}
INDIRECT_JUMP = re.compile(r"^(?:jalr|jr)\s+(-?\d+)\(([^)]+)\)")
BLOCK_ENDS = BRANCHES | {"jal", "jalr", "jr", "ret"}
DIRECT_TARGET = re.compile(r"(?:^|,)\s*([0-9a-f]+)(?:\s|$)")


def split_control_flow_range(
    instructions: list[tuple[int, str]], lower: int, upper: int,
    max_instructions: int,
) -> list[tuple[int, int]]:
    """Split one address range at control flow and bounded-size checkpoints."""
    pcs = [pc for pc, _ in instructions if lower <= pc < upper]
    if not pcs:
        return []
    boundaries = {lower, upper}
    for pc, instruction in instructions:
        if not lower <= pc < upper:
            continue
        opcode = instruction.split(maxsplit=1)[0]
        if opcode in BLOCK_ENDS:
            boundaries.add(min(pc + 4, upper))
            if opcode in BRANCHES:
                targets = DIRECT_TARGET.findall(instruction)
                if targets:
                    target = int(targets[-1], 16)
                    if lower <= target < upper:
                        boundaries.add(target)
    for index in range(max_instructions, len(pcs), max_instructions):
        boundaries.add(pcs[index])
    ordered = sorted(boundaries)
    return [(start, stop) for start, stop in zip(ordered, ordered[1:])
            if any(start <= pc < stop for pc in pcs)]


def cfg_ranges(cfg: dict[str, object], profile: dict[str, object]) -> tuple[
    list[tuple[int, int]], int
]:
    """Select reviewed regions and proof blocks from the generated CFG."""
    functions = {function["name"]: function for function in cfg["functions"]}
    ranges = []
    for region in profile.get("cfgRegions", []):
        function = functions[region["function"]]
        if "block" in region:
            block = function["blocks"][region["block"]]
            ranges.append((block["start"], block["end"]))
        else:
            ranges.append((function["start"], function["start"] + function["size"]))
    reviewed_count = len(ranges)
    for selection in profile.get("cfgBlockFunctions", []):
        if isinstance(selection, str):
            name, maximum = selection, None
        else:
            name = selection["function"]
            maximum = selection.get("maxInstructions")
        for block in functions[name]["blocks"]:
            instructions = block["instructions"]
            if maximum is None:
                ranges.append((block["start"], block["end"]))
                continue
            for offset in range(0, len(instructions), maximum):
                start = instructions[offset]["pc"]
                stop = (instructions[offset + maximum]["pc"]
                        if offset + maximum < len(instructions)
                        else block["end"])
                ranges.append((start, stop))
    for region in profile.get("cfgPostRegions", []):
        function = functions[region["function"]]
        if "block" in region:
            block = function["blocks"][region["block"]]
            ranges.append((block["start"], block["end"]))
        else:
            ranges.append((function["start"], function["start"] + function["size"]))
    return ranges, reviewed_count


def control_flow_constraints(
    instruction: str, return_register: str | None, program_counter: str | None,
    jump_registers: dict[str, str] | None = None,
) -> list[str]:
    opcode = instruction.split(maxsplit=1)[0]
    if opcode == "ret" and return_register is not None:
        return [f"= ((_ extract 1 0) {return_register}) 0b00"]
    if opcode in BRANCHES and program_counter is not None:
        return [f"= ((_ extract 1 0) {program_counter}) 0b00"]
    jump = INDIRECT_JUMP.match(instruction)
    if jump is not None and jump_registers is not None:
        offset_text, base = jump.groups()
        register = jump_registers.get(base)
        if register is not None:
            offset = int(offset_text) % (1 << 64)
            target = f"(bvadd {register} 0x{offset:016x})"
            return [f"= ((_ extract 1 0) {target}) 0b00"]
    return []


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--disassembly", required=True)
    parser.add_argument("--profile", required=True)
    parser.add_argument("--cfg")
    outputs = parser.add_mutually_exclusive_group(required=True)
    outputs.add_argument("--output")
    outputs.add_argument("--split-output-dir")
    args = parser.parse_args()

    profile = json.loads(Path(args.profile).read_text())
    disassembly = Path(args.disassembly).read_text().splitlines()
    instructions = []
    for line in disassembly:
        match = INSTRUCTION.match(line)
        if match is not None:
            instructions.append((int(match.group(1), 16), match.group(2)))
    if args.cfg:
        ranges, base_range_count = cfg_ranges(
            json.loads(Path(args.cfg).read_text()), profile
        )
    else:
        ranges = [(int(a, 0), int(b, 0)) for a, b in profile["ranges"]]
        base_range_count = len(ranges)
    for split_range in profile.get("splitRanges", []):
        ranges.extend(split_control_flow_range(
            instructions,
            int(split_range["start"], 0),
            int(split_range["end"], 0),
            split_range.get("maxInstructions", 32),
        ))
    selected = [[] for _ in ranges]

    for line in disassembly:
        match = INSTRUCTION.match(line)
        if match is None:
            continue
        pc = int(match.group(1), 16)
        range_indexes = [index for index, (lower, upper) in enumerate(ranges)
                         if lower <= pc < upper]
        if not range_indexes:
            continue
        instruction = match.group(2)
        annotations = []
        annotations.extend(
            f"//@constraint: {constraint}"
            for constraint in effective_address_constraints(
                instruction, profile.get("memoryBaseRegisters", {}))
        )
        annotations.extend(
            f"//@constraint: {constraint}"
            for constraint in control_flow_constraints(
                instruction,
                profile.get("alignedReturnRegister"),
                profile.get("alignedProgramCounter"),
                profile.get("controlFlowRegisters", {}),
            )
        )
        for base, constraints in profile.get("constraintsByMemoryBase", {}).items():
            if f"({base})" in instruction:
                annotations.extend(f"//@constraint: {constraint}"
                                   for constraint in constraints)
        for index in range_indexes:
            spec_annotations = configured_spec_annotations(pc, profile)
            if (profile.get("useLoadStoreSpecs", False)
                    and index >= base_range_count):
                array_view = load_array_view(pc, profile)
                spec_annotations.extend(load_store_spec_annotations(
                    instruction, profile.get("memoryBaseRegisters", {}), array_view))
                spec_annotations.extend(jump_spec_annotations(
                    instruction, profile.get("controlFlowRegisters", {})))
            selected[index].extend(spec_annotations + annotations + [line])

    header = [f'//@isla-config: {profile["islaConfig"]}']
    if args.output:
        lines = list(header)
        for block in selected:
            lines.extend(block)
        Path(args.output).parent.mkdir(parents=True, exist_ok=True)
        write_text_if_changed(Path(args.output), "\n".join(lines) + "\n")
    else:
        output_dir = Path(args.split_output_dir)
        output_dir.mkdir(parents=True, exist_ok=True)
        expected = {output_dir / f"block_{index:02}.dump"
                    for index in range(len(selected))}
        for stale in set(output_dir.glob("block_*.dump")) - expected:
            stale.unlink()
        for index, block in enumerate(selected):
            write_text_if_changed(
                output_dir / f"block_{index:02}.dump",
                "\n".join(header + block) + "\n",
            )


if __name__ == "__main__":
    main()
