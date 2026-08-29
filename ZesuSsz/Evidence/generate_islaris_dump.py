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


def control_flow_constraints(
    instruction: str, return_register: str | None, program_counter: str | None
) -> list[str]:
    opcode = instruction.split(maxsplit=1)[0]
    if opcode == "ret" and return_register is not None:
        return [f"= ((_ extract 1 0) {return_register}) 0b00"]
    if opcode in BRANCHES and program_counter is not None:
        return [f"= ((_ extract 1 0) {program_counter}) 0b00"]
    return []


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--disassembly", required=True)
    parser.add_argument("--profile", required=True)
    outputs = parser.add_mutually_exclusive_group(required=True)
    outputs.add_argument("--output")
    outputs.add_argument("--split-output-dir")
    args = parser.parse_args()

    profile = json.loads(Path(args.profile).read_text())
    ranges = [(int(a, 0), int(b, 0)) for a, b in profile["ranges"]]
    selected = [[] for _ in ranges]

    for line in Path(args.disassembly).read_text().splitlines():
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
            )
        )
        for base, constraints in profile.get("constraintsByMemoryBase", {}).items():
            if f"({base})" in instruction:
                annotations.extend(f"//@constraint: {constraint}"
                                   for constraint in constraints)
        for index in range_indexes:
            selected[index].extend(annotations + [line])

    header = f'//@isla-config: {profile["islaConfig"]}'
    if args.output:
        lines = [header]
        for block in selected:
            lines.extend(block)
        Path(args.output).parent.mkdir(parents=True, exist_ok=True)
        Path(args.output).write_text("\n".join(lines) + "\n")
    else:
        output_dir = Path(args.split_output_dir)
        output_dir.mkdir(parents=True, exist_ok=True)
        for index, block in enumerate(selected):
            (output_dir / f"block_{index:02}.dump").write_text(
                "\n".join([header] + block) + "\n")


if __name__ == "__main__":
    main()
