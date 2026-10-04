#!/usr/bin/env python3
"""Generate checked decodeItem CFG hints from the selected root inventory."""

import argparse
import hashlib
import json
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
INVENTORY = ROOT / "build/stock-zisk/inventory.json"
OUTPUT = ROOT / "ZesuSsz/Evidence/decode_item_block_design.json"


def address(value: int) -> str:
    return f"0x{value:08x}"


# Each expression refers to register values just before the source branch.
# The source instruction and destination come from the inventory, not here.
GUARDS = {
    0x800D6970: {0x800D6AE0: ("eq", "x12", "0"),
                 0x800D6974: ("ne", "x12", "0")},
    0x800D6978: {0x800D69A4: ("s_lt", "x13", "0"),
                 0x800D697C: ("s_ge", "x13", "0")},
    0x800D69AC: {0x800D69D8: ("ne", "x13", "x14"),
                 0x800D69B0: ("eq", "x13", "x14")},
    0x800D69DC: {0x800D6A00: ("u_lt", "x14", "x13"),
                 0x800D69E0: ("u_ge", "x14", "x13")},
    0x800D69E4: {0x800D6AE0: ("u_ge", "x13", "x12"),
                 0x800D69E8: ("u_lt", "x13", "x12")},
    0x800D6A04: {0x800D6A64: ("u_ge", "x13", "x14"),
                 0x800D6A08: ("u_lt", "x13", "x14")},
    0x800D6A10: {0x800D6AE0: ("u_ge", "x14", "x12"),
                 0x800D6A14: ("u_lt", "x14", "x12")},
    0x800D6A34: {0x800D6A24: ("ne", "x15", "x11"),
                 0x800D6A38: ("eq", "x15", "x11")},
    0x800D6A3C: {0x800D6AE0: ("u_lt", "x12", "x14"),
                 0x800D6A40: ("u_ge", "x12", "x14")},
    0x800D6A68: {0x800D6AA8: ("u_ge", "x13", "x14"),
                 0x800D6A6C: ("u_lt", "x13", "x14")},
    0x800D6A74: {0x800D6AE0: ("u_ge", "x13", "x12"),
                 0x800D6A78: ("u_lt", "x13", "x12")},
    0x800D6AB0: {0x800D6AE0: ("u_ge", "x14", "x12"),
                 0x800D6AB4: ("u_lt", "x14", "x12")},
    0x800D6AD4: {0x800D6AC4: ("ne", "x15", "x11"),
                 0x800D6AD8: ("eq", "x15", "x11")},
    0x800D6ADC: {0x800D6B08: ("u_ge", "x12", "x14"),
                 0x800D6AE0: ("u_lt", "x12", "x14")},
}

CLASSES = {
    0x800D6960: "entry_prologue",
    0x800D6974: "prefix_load",
    0x800D697C: "literal_byte_write",
    0x800D698C: "literal_or_short_string_return",
    0x800D69A4: "high_prefix_dispatch",
    0x800D69B0: "empty_string_return",
    0x800D69D8: "short_string_class_test",
    0x800D69E0: "short_string_length_test",
    0x800D69E8: "short_string_write",
    0x800D6A00: "list_or_long_string_dispatch",
    0x800D6A08: "long_string_width_test",
    0x800D6A14: "long_string_fold_initialization",
    0x800D6A24: "long_string_fold_header",
    0x800D6A38: "long_string_length_check",
    0x800D6A40: "long_string_return",
    0x800D6A64: "short_or_long_list_dispatch",
    0x800D6A6C: "short_list_length_test",
    0x800D6A78: "short_list_return",
    0x800D6AA8: "long_list_width_test",
    0x800D6AB4: "long_list_fold_initialization",
    0x800D6AC4: "long_list_fold_header",
    0x800D6AD8: "long_list_length_check",
    0x800D6AE0: "error_return",
    0x800D6B08: "long_list_return",
}

RETURN_CLAUSES = {
    0x800D698C: {
        "contract": "C1AResult or C1BResult / candidateResult40 / successResult40",
        "cases": [
            {"incoming_from": address(0x800D697C),
             "candidate": "candidateSuccess false 0 1", "payload_pointer": "inputPointer"},
            {"incoming_from": address(0x800D69E8),
             "candidate": "candidateSuccess false 1 (prefix - 128)",
             "payload_pointer": "inputPointer + 1"},
        ],
    },
    0x800D69B0: {
        "contract": "C1AResult or C1BResult / candidateResult40 / successResult40",
        "cases": [{"candidate": "candidateSuccess false 1 0",
                   "payload_pointer": "1 (empty-string sentinel)"}],
    },
    0x800D6A40: {
        "contract": "C1AResult or C1BResult / candidateResult40 / successResult40",
        "cases": [{"candidate": "candidateSuccess false (1 + width) bigEndian(lengthBytes)",
                   "payload_pointer": "inputPointer + 1 + width",
                   "wrap": "C1A requires headerFits; C1B records binaryWrapCase"}],
    },
    0x800D6A78: {
        "contract": "C1AResult or C1BResult / candidateResult40 / successResult40",
        "cases": [{"candidate": "candidateSuccess true 1 (prefix - 192)",
                   "payload_pointer": "inputPointer + 1"}],
    },
    0x800D6AE0: {
        "contract": "C1AResult or C1BResult / candidateResult40 / errorResult40",
        "cases": [{"candidate": "candidateError", "error_byte_at_32": 4}],
    },
    0x800D6B08: {
        "contract": "C1AResult or C1BResult / candidateResult40 / successResult40",
        "cases": [{"candidate": "candidateSuccess true (1 + width) bigEndian(lengthBytes)",
                   "payload_pointer": "inputPointer + 1 + width",
                   "wrap": "C1A requires headerFits; C1B records binaryWrapCase"}],
    },
}

LOOP_HINTS = {
    0x800D6A24: {
        "header_pc": address(0x800D6A24),
        "rocq_predicate": "ZesuSsz.Contracts.RlpDecodeItemByteFoldSites.decodeItemStringFoldAt",
        "header_resource": "ZesuSsz.Contracts.RlpDecodeItemByteFold.decodeItemByteFoldResources",
        "init_resource": "ZesuSsz.Contracts.RlpDecodeItemByteFoldBlocks.decodeItemFoldInitResources",
        "checked_resource": "ZesuSsz.Contracts.RlpDecodeItemByteFoldBlocks.decodeItemFoldCheckedResources",
        "pure_lemmas": {
            "entry": "ZesuSsz.Proofs.DecodeItem.ByteFoldPure.decodeItem_fold_entry",
            "preservation": "ZesuSsz.Proofs.DecodeItem.ByteFoldPure.decodeItem_fold_preservation",
            "exit": "ZesuSsz.Proofs.DecodeItem.ByteFoldPure.decodeItem_fold_exit",
        },
        "machine_obligations": {
            "entry": "ZesuSsz.Proofs.DecodeItem.ByteFoldMachineObligations.decodeItemStringFoldEntry",
            "preservation": "ZesuSsz.Proofs.DecodeItem.ByteFoldMachineObligations.decodeItemStringFoldPreservation",
            "exit": "ZesuSsz.Proofs.DecodeItem.ByteFoldMachineObligations.decodeItemStringFoldExit",
        },
        "symbolic_parameters": {
            "i": {"register": "x15", "register_value": "payloadStart + i"},
            "n": {"register": "x14", "register_value": "n + 1"},
            "pointer": {"symbol": "payloadStart", "register_bindings": {
                "x11": "payloadStart + n", "x15": "payloadStart + i"}},
            "accumulator": {"register": "x13", "register_value": "bigEndian(firstn i lengthBytes)"},
        },
        "body_edge_condition": "i < n",
        "preheader": address(0x800D6A14), "backedge": address(0x800D6A34),
        "exit": address(0x800D6A38),
        "register_bindings": {"x10": "outputPointer", "x11": "payloadStart + n",
                              "x12": "inputLength", "x13": "bigEndian(firstn i lengthBytes)",
                              "x14": "n + 1", "x15": "payloadStart + i",
                              "x16": "arbitrary loaded byte register",
                              "x2": "stackPointer - 16", "x1": "returnAddress",
                              "x8": "stackPointer"},
        "body_guard": "0 <= i < n <= 8 and 1 <= n",
    },
    0x800D6AC4: {
        "header_pc": address(0x800D6AC4),
        "rocq_predicate": "ZesuSsz.Contracts.RlpDecodeItemByteFoldSites.decodeItemListFoldAt",
        "header_resource": "ZesuSsz.Contracts.RlpDecodeItemByteFold.decodeItemByteFoldResources",
        "init_resource": "ZesuSsz.Contracts.RlpDecodeItemByteFoldBlocks.decodeItemFoldInitResources",
        "checked_resource": "ZesuSsz.Contracts.RlpDecodeItemByteFoldBlocks.decodeItemFoldCheckedResources",
        "pure_lemmas": {
            "entry": "ZesuSsz.Proofs.DecodeItem.ByteFoldPure.decodeItem_fold_entry",
            "preservation": "ZesuSsz.Proofs.DecodeItem.ByteFoldPure.decodeItem_fold_preservation",
            "exit": "ZesuSsz.Proofs.DecodeItem.ByteFoldPure.decodeItem_fold_exit",
        },
        "machine_obligations": {
            "entry": "ZesuSsz.Proofs.DecodeItem.ByteFoldMachineObligations.decodeItemListFoldEntry",
            "preservation": "ZesuSsz.Proofs.DecodeItem.ByteFoldMachineObligations.decodeItemListFoldPreservation",
            "exit": "ZesuSsz.Proofs.DecodeItem.ByteFoldMachineObligations.decodeItemListFoldExit",
        },
        "symbolic_parameters": {
            "i": {"register": "x15", "register_value": "payloadStart + i"},
            "n": {"register": "x14", "register_value": "n + 1"},
            "pointer": {"symbol": "payloadStart", "register_bindings": {
                "x11": "payloadStart + n", "x15": "payloadStart + i"}},
            "accumulator": {"register": "x13", "register_value": "bigEndian(firstn i lengthBytes)"},
        },
        "body_edge_condition": "i < n",
        "preheader": address(0x800D6AB4), "backedge": address(0x800D6AD4),
        "exit": address(0x800D6AD8),
        "register_bindings": {"x10": "outputPointer", "x11": "payloadStart + n",
                              "x12": "inputLength", "x13": "bigEndian(firstn i lengthBytes)",
                              "x14": "n + 1", "x15": "payloadStart + i",
                              "x16": "arbitrary loaded byte register",
                              "x2": "stackPointer - 16", "x1": "returnAddress",
                              "x8": "stackPointer"},
        "body_guard": "0 <= i < n <= 8 and 1 <= n",
    },
}

BRANCH_CONSTANTS = {
    0x800D69AC: {"x14": 128},
    0x800D69DC: {"x14": 183},
    0x800D6A04: {"x14": 192},
    0x800D6A68: {"x14": 248},
}


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def register_reads(row: dict) -> set[int]:
    mnemonic = row["mnemonic"]
    if mnemonic in {"addi", "andi", "slli", "lb", "lbu", "ld", "jalr"}:
        return {row["rs1"]} - {0}
    if mnemonic in {"sd", "sh", "sb", "add", "or", "beq", "bne", "blt",
                    "bltu", "bgeu"}:
        return {row["rs1"], row["rs2"]} - {0}
    if mnemonic == "jal":
        return set()
    raise RuntimeError(f"unknown decodeItem instruction: {mnemonic}")


def register_write(row: dict) -> set[int]:
    if row["kind"] in {"plain", "load"}:
        return {row["rd"]} - {0}
    return set()


def local_register_use(rows: list[dict]) -> tuple[set[int], set[int]]:
    reads, writes = set(), set()
    for row in rows:
        reads.update(register_reads(row) - writes)
        writes.update(register_write(row))
    return reads, writes


def expected_branch_guards(row: dict) -> list[tuple[str, str, str]]:
    operations = {
        "beq": ("eq", "ne"), "bne": ("ne", "eq"),
        "blt": ("s_lt", "s_ge"), "bltu": ("u_lt", "u_ge"),
        "bgeu": ("u_ge", "u_lt"),
    }
    taken, fallthrough = operations[row["mnemonic"]]
    left = "0" if row["rs1"] == 0 else f"x{row['rs1']}"
    right = "0" if row["rs2"] == 0 else f"x{row['rs2']}"
    return [(taken, left, right), (fallthrough, left, right)]


def build() -> dict:
    inventory = json.loads(INVENTORY.read_text())
    function = next(f for f in inventory["functions"] if f["name"] == "rlp.decodeItem")
    blocks = sorted(function["blocks"], key=lambda b: b["start"])
    starts = {b["start"] for b in blocks}
    if len(blocks) != 24 or set(CLASSES) != starts or len(function["rows"]) != 116:
        raise RuntimeError("decodeItem inventory changed its reviewed 24-block shape")
    if blocks[0]["start"] != function["entry"] or blocks[-1]["end"] != function["end"]:
        raise RuntimeError("block table no longer spans the decodeItem region")
    if any(left["end"] != right["start"] for left, right in zip(blocks, blocks[1:])):
        raise RuntimeError("block table has a gap or overlap")
    if function["branch_count"] != 14 or function["loop_count"] != 2:
        raise RuntimeError("decodeItem branch or loop count changed")
    if inventory["elf_sha256"] != sha256(ROOT / "build/stock-zisk/zesu-zisk.elf"):
        raise RuntimeError("inventory and selected ELF hashes differ")
    if set(GUARDS) != {b["end"] - 4 for b in blocks
                       if next(r for r in function["rows"] if r["pc"] == b["end"] - 4)["kind"] == "branch"}:
        raise RuntimeError("conditional guard map does not cover the CFG")
    if set(RETURN_CLAUSES) != {b["start"] for b in blocks if not b["successors"]}:
        raise RuntimeError("return clause map does not cover all returns")
    if set(function["returns"]) != {b["end"] - 4 for b in blocks if not b["successors"]}:
        raise RuntimeError("return PCs changed")
    if set(LOOP_HINTS) != {int(loop["minimum_pc"], 16) for loop in function["loops"]}:
        raise RuntimeError("loop hint map does not cover both inventory loops")
    loop_edges = {(edge["from"], edge["to"]) for loop in function["loops"]
                  for edge in loop["backward_edges"]}

    incoming: dict[int, list[dict]] = {start: [] for start in starts}
    uses, defs = {}, {}
    for block in blocks:
        start, end = block["start"], block["end"]
        rows = [row for row in function["rows"] if start <= row["pc"] < end]
        if not rows or rows[-1]["pc"] != end - 4 or rows[-1]["successors"] != block["successors"]:
            raise RuntimeError(f"invalid block boundary or successors at {address(start)}")
        if len(rows) != (end - start) // 4:
            raise RuntimeError(f"instruction gap at {address(start)}")
        uses[start], defs[start] = local_register_use(rows)
        branch_pc = rows[-1]["pc"]
        if rows[-1]["kind"] == "branch":
            if set(GUARDS[branch_pc]) != set(block["successors"]):
                raise RuntimeError(f"branch targets changed at {address(branch_pc)}")
            for target, expected in zip(block["successors"], expected_branch_guards(rows[-1])):
                if GUARDS[branch_pc][target] != expected:
                    raise RuntimeError(f"branch guard changed at {address(branch_pc)}")
        for target in block["successors"]:
            if target not in starts:
                raise RuntimeError(f"edge leaves the block table: {address(target)}")
            guard = GUARDS.get(branch_pc, {}).get(target)
            if (address(branch_pc), address(target)) in loop_edges:
                kind = "loop_backedge"
            elif guard:
                kind = "conditional"
            elif rows[-1]["mnemonic"] == "jal":
                kind = "jump"
            else:
                kind = "fallthrough"
            edge = {"from_block": address(start), "from_instruction": address(branch_pc),
                    "source_terminator": rows[-1]["mnemonic"], "kind": kind,
                    "path_condition": {"op": guard[0], "left": guard[1], "right": guard[2]}
                    if guard else {"op": "true"}}
            incoming[target].append(edge)

    # Register use is a hint, not an ownership proof. The explicit frame
    # and array resources remain part of every post-prologue state.
    live_in = {start: set() for start in starts}
    changed = True
    while changed:
        changed = False
        for block in reversed(blocks):
            start = block["start"]
            out = set().union(*(live_in[target] for target in block["successors"]))
            new = uses[start] | (out - defs[start])
            if new != live_in[start]:
                live_in[start], changed = new, True

    rows_out = []
    for block in blocks:
        start = block["start"]
        row = {
            "entry_pc": address(start), "end_pc_exclusive": address(block["end"]),
            "entry_class": CLASSES[start],
            "incoming_edges": sorted(incoming[start], key=lambda edge: (
                edge["from_block"], edge["from_instruction"])),
            "successor_pcs": [address(target) for target in block["successors"]],
            "needed_resources": {
                "register_live_in_hint": [f"x{reg}" for reg in sorted(live_in[start])],
                "system_register_collection": "reg_col zesu_sys_regs",
                "input": "decodeItemInputPointer args ↦ₘ∗ decodeItemInputBytes args",
                "output": "owned 40-byte result array at decodeItemOutputPointer args",
                "stack": "(stackPointer - 16) ↦ₘ? 16" if start == function["entry"]
                         else "(stackPointer - 16) ↦ₘ∗ frameBytes; length frameBytes = 16",
                "return_continuation": "decodeItemReturnAddress args and saved x8",
            },
        }
        if start == function["entry"]:
            row["incoming_edges"] = [{"from_block": "caller", "from_instruction": None,
                                      "kind": "entry", "path_condition": {"op": "true"}}]
            row["needed_resources"]["rocq_entry"] = (
                "ZesuSsz.Contracts.RlpDecodeItemContract.decodeItemEntryResources")
        if start in LOOP_HINTS:
            row["invariant_hint"] = LOOP_HINTS[start]
        branch_pc = block["end"] - 4
        if branch_pc in BRANCH_CONSTANTS:
            row["branch_constant_facts"] = BRANCH_CONSTANTS[branch_pc]
        if start in RETURN_CLAUSES:
            row["return_clause"] = {"return_instruction_pc": address(block["end"] - 4),
                                    **RETURN_CLAUSES[start]}
        rows_out.append(row)

    hashes = {
        "inventory_sha256": sha256(INVENTORY),
        "selected_elf_sha256": inventory["elf_sha256"],
        "raw_dump_sha256": sha256(ROOT / "build/stock-zisk/decodeItem.raw.dump"),
        "level1_contract_sha256": sha256(ROOT / "ZesuSsz/Contracts/RlpDecodeItemContract.v"),
        "byte_fold_schema_sha256": sha256(ROOT / "ZesuSsz/Contracts/RlpDecodeItemByteFold.v"),
        "byte_fold_sites_sha256": sha256(ROOT / "ZesuSsz/Contracts/RlpDecodeItemByteFoldSites.v"),
        "byte_fold_blocks_sha256": sha256(ROOT / "ZesuSsz/Contracts/RlpDecodeItemByteFoldBlocks.v"),
        "byte_fold_pure_sha256": sha256(ROOT / "ZesuSsz/Proofs/DecodeItem/ByteFoldPure.v"),
        "byte_fold_machine_obligations_sha256": sha256(
            ROOT / "ZesuSsz/Proofs/DecodeItem/ByteFoldMachineObligations.v"),
        "generator_sha256": sha256(Path(__file__)),
    }
    return {
        "schema_version": 1,
        "label": "Static CFG design and invariant hints; no block proof or ELF execution",
        "proof_status": "design_only",
        "source_inventory": "build/stock-zisk/inventory.json",
        "function": "rlp.decodeItem", "entry_pc": address(function["entry"]),
        "end_pc_exclusive": address(function["end"]),
        "instruction_count": function["instruction_count"],
        "block_count": function["block_count"],
        "conditional_branch_count": function["branch_count"],
        "loop_count": function["loop_count"],
        "edge_condition_scope": "register values before the source block's final instruction",
        "condition_ops": {"eq": "equal bits", "ne": "unequal bits",
                          "s_lt": "signed less than", "s_ge": "signed greater or equal",
                          "u_lt": "unsigned less than", "u_ge": "unsigned greater or equal",
                          "true": "unconditional"},
        "hashes": hashes, "blocks": rows_out,
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    rendered = json.dumps(build(), indent=2) + "\n"
    if args.check:
        if not OUTPUT.exists() or OUTPUT.read_text() != rendered:
            raise SystemExit("decodeItem block design is stale")
        print(f"checked {OUTPUT.relative_to(ROOT)}")
    else:
        OUTPUT.write_text(rendered)
        print(f"wrote {OUTPUT.relative_to(ROOT)}")


if __name__ == "__main__":
    main()
