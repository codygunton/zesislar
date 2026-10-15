#!/usr/bin/env python3
"""Generate a selected function's CFG from words and explicit entry metadata."""
import argparse
from copy import deepcopy
import hashlib
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "tools/block"))
from function_names import FunctionNames, prefix_argument
from generate_table import control, structure
from entry_bindings import validate_design


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def checked_design_text(text):
    """Ignore only the producer hash while preserving every other byte."""
    decoder = json.JSONDecoder()

    def member_span(start, wanted):
        position = start + 1
        found = None
        keys = set()
        while True:
            while text[position].isspace():
                position += 1
            if text[position] == "}":
                break
            key, position = decoder.raw_decode(text, position)
            if key in keys:
                raise ValueError("The block design contains a duplicate JSON key.")
            keys.add(key)
            while text[position].isspace():
                position += 1
            if text[position] != ":":
                raise ValueError("The block design contains an invalid JSON member.")
            position += 1
            while text[position].isspace():
                position += 1
            value_start = position
            _, position = decoder.raw_decode(text, position)
            if key == wanted:
                found = (value_start, position)
            while text[position].isspace():
                position += 1
            if text[position] == ",":
                position += 1
        if found is None:
            raise ValueError(f"The block design omits {wanted}.")
        return found

    parsed = json.loads(text)
    value = parsed["hashes"]["generator_sha256"]
    if not isinstance(value, str) or len(value) != 64 or any(c not in "0123456789abcdef" for c in value):
        raise ValueError("The generator hash must contain 64 lowercase hexadecimal digits.")
    start = len(text) - len(text.lstrip())
    hashes_start, _ = member_span(start, "hashes")
    first, last = member_span(hashes_start, "generator_sha256")
    return text[:first] + '"<generator_sha256>"' + text[last:]


def address(value):
    return f"0x{value:08x}"


def selected_function(inventory, name):
    matches = [row for row in inventory["functions"] if row["name"] == name]
    if not matches:
        matches = [row for row in inventory["functions"]
                   if row["name"].rsplit(".", 1)[-1] == name]
    if len(matches) != 1:
        raise ValueError("The inventory must contain one selected function.")
    return matches[0]


def register_reads(row):
    mnemonic = row["mnemonic"]
    if mnemonic in {"lui", "auipc", "jal"}:
        return set()
    if mnemonic in {"addi", "andi", "xori", "sltiu", "slli", "lb", "lbu", "lhu", "ld", "jalr", "csrrs"}:
        return {row["rs1"]} - {0}
    if mnemonic in {"sd", "sh", "sb", "add", "sub", "or", "and", "sll", "sltu", "beq", "bne", "blt", "bge", "bltu", "bgeu"}:
        return {row["rs1"], row["rs2"]} - {0}
    raise ValueError(f"Unsupported selected instruction: {mnemonic}.")


def source_hashes(paths, root):
    result = {}
    for name in paths:
        path = Path(name)
        if path.is_absolute() or ".." in path.parts:
            raise ValueError("The source path must stay inside the workspace.")
        source = (root / path).resolve()
        if not source.is_relative_to(root.resolve()) or not source.is_file():
            raise ValueError(f"The bound source is unavailable: {name}.")
        result[name] = digest(source)
    return result


def build(inventory, name, profile, *, root=ROOT, generator=None):
    """Preserve supplied resource declarations while checking the selected CFG."""
    root = Path(root)
    function = selected_function(inventory, name)
    if profile.get("function") != function["name"]:
        raise ValueError("The profile and inventory name different functions.")
    result = deepcopy(profile["design"])
    blocks = sorted(function["blocks"], key=lambda block: block["start"])
    rows = {row["pc"]: row for row in function["rows"]}
    starts = {block["start"] for block in blocks}
    templates = {int(row["entry_pc"], 0): row for row in result["blocks"]}
    if len(templates) != len(result["blocks"]) or set(templates) != starts:
        raise ValueError("The profile must describe every selected block exactly once.")
    if len(rows) != len(function["rows"]) or set(rows) != set(range(function["entry"], function["end"], 4)):
        raise ValueError("The selected instructions have a gap or a duplicate.")
    if blocks[0]["start"] != function["entry"] or blocks[-1]["end"] != function["end"]:
        raise ValueError("The blocks do not span the selected function.")
    if any(left["end"] != right["start"] for left, right in zip(blocks, blocks[1:])):
        raise ValueError("The selected blocks have a gap or an overlap.")
    if inventory["elf_sha256"] != digest(root / "build/stock-zisk/zesu-zisk.elf"):
        raise ValueError("The inventory binds a different selected ELF.")

    incoming = {pc: [] for pc in starts}
    uses, writes, terminators = {}, {}, {}
    backedges = {(int(edge["from"], 0), int(edge["to"], 0))
                 for loop in function["loops"] for edge in loop["backward_edges"]}
    branch_count, returns = 0, []
    for block in blocks:
        pc, stop = block["start"], block["end"]
        uses[pc], writes[pc] = set(), set()
        for at in range(pc, stop, 4):
            row = rows[at]
            kind, targets, _, _ = control(row)
            if row["kind"] != kind or set(row["successors"]) != set(targets):
                raise ValueError(f"The instruction word and CFG differ at {address(at)}.")
            if at + 4 != stop and targets != [at + 4]:
                raise ValueError("A control transfer occurs inside a block.")
            uses[pc].update(register_reads(row) - writes[pc])
            if kind in {"plain", "load"}:
                writes[pc].update({row["rd"]} - {0})
        tail = rows[stop - 4]
        kind, targets, guards, _ = control(tail)
        terminators[pc] = kind
        if set(block["successors"]) != set(targets) or any(target not in starts for target in targets):
            raise ValueError("A block has an undeclared successor.")
        branch_count += kind == "branch"
        if kind == "return":
            returns.append(tail["pc"])
        for target, guard in zip(targets, guards):
            edge_kind = ("loop_backedge" if (tail["pc"], target) in backedges else
                         "conditional" if kind == "branch" else
                         "jump" if kind == "jump" else "fallthrough")
            incoming[target].append({"from_block": address(pc),
                "from_instruction": address(tail["pc"]), "source_terminator": tail["mnemonic"],
                "kind": edge_kind, "path_condition": guard})
    if sorted(returns) != sorted(function["returns"]) or branch_count != function["branch_count"]:
        raise ValueError("The selected branch or return inventory differs from the words.")

    live = {pc: set() for pc in starts}
    changed = True
    while changed:
        changed = False
        for block in reversed(blocks):
            pc = block["start"]
            successors = set().union(*(live[target] for target in block["successors"]))
            current = uses[pc] | (successors - writes[pc])
            if current != live[pc]:
                live[pc], changed = current, True
    output = []
    for block in blocks:
        pc = block["start"]
        row = deepcopy(templates[pc])
        selected = {(edge["from_block"], edge["from_instruction"]): edge["resource_alternative"]
                    for edge in row.get("incoming_edges", []) if "resource_alternative" in edge}
        edges = sorted(incoming[pc], key=lambda edge: (edge["from_block"], edge["from_instruction"]))
        for edge in edges:
            key = (edge["from_block"], edge["from_instruction"])
            if key in selected:
                edge["resource_alternative"] = selected.pop(key)
        if selected:
            raise ValueError("A resource alternative names an absent incoming edge.")
        if pc == function["entry"]:
            edges.insert(0, {"from_block": "caller", "from_instruction": None,
                             "kind": "entry", "path_condition": {"op": "true"}})
        row.update(entry_pc=address(pc), end_pc_exclusive=address(block["end"]),
                   incoming_edges=edges, successor_pcs=[address(target) for target in block["successors"]])
        row.setdefault("needed_resources", {})["register_live_in_hint"] = [f"x{reg}" for reg in sorted(live[pc])]
        row["source_hashes"] = source_hashes(row["source_hashes"], root)
        if terminators[pc] == "return":
            row["return_clause"]["return_instruction_pc"] = address(block["end"] - 4)
        elif "return_clause" in row:
            raise ValueError("A non-return block has a return clause.")
        output.append(row)
    result.update(function=function["name"], entry_pc=address(function["entry"]),
                  end_pc_exclusive=address(function["end"]), instruction_count=len(rows),
                  block_count=len(blocks), conditional_branch_count=branch_count,
                  loop_count=function["loop_count"], blocks=output)
    refreshed = source_hashes(profile["hash_sources"].values(), root)
    result["hashes"] = {key: refreshed[path] for key, path in profile["hash_sources"].items()}
    result["hashes"]["generator_sha256"] = digest(generator or Path(__file__))
    convention = result["table_convention"]
    convention["code_source_hashes"] = source_hashes(convention["code_source_hashes"], root)
    structure(inventory, result)
    validate_design(result, root)
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--function", required=True)
    parser.add_argument("--inventory", type=Path, default=ROOT / "build/stock-zisk/inventory.json")
    parser.add_argument("--profile", type=Path)
    parser.add_argument("--output", type=Path)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    names = FunctionNames(prefix_argument(args.function))
    profile_path = args.profile or ROOT / f"ZesuSsz/Contracts/{names.filename}_block_design.json"
    profile = json.loads(profile_path.read_text())
    rendered = json.dumps(build(json.loads(args.inventory.read_text()), args.function, profile), indent=2) + "\n"
    output = (args.output or ROOT / f"ZesuSsz/Evidence/{names.filename}_block_design.json").resolve()
    label = output.relative_to(ROOT) if output.is_relative_to(ROOT) else output
    if args.check:
        if not output.is_file() or checked_design_text(output.read_bytes().decode("utf-8")) != checked_design_text(rendered):
            raise SystemExit("The selected block design is stale.")
        print(f"checked {label}")
    else:
        output.parent.mkdir(parents=True, exist_ok=True)
        output.write_text(rendered)
        print(f"wrote {label}")


if __name__ == "__main__":
    main()
