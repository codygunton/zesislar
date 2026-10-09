#!/usr/bin/env python3
"""Check block-table structure against the bound decodeItem instruction words.

Coverage is structural evidence. It does not prove a block contract or an edge
adapter. Resource-table rendering requires supplied executable declarations.
"""
from __future__ import annotations

import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import entry_schema

ROOT = Path(__file__).resolve().parents[2]


def address(value):
    return int(value, 0) if isinstance(value, str) else value


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def path_label(path):
    try:
        return str(Path(path).resolve().relative_to(ROOT))
    except ValueError:
        return Path(path).name


def entry_source_hashes(design, root=ROOT):
    """Check supplied declaration sources without inventing source locations."""
    hashes = {}
    for block in design["blocks"]:
        if not block.get("entry_definition"):
            continue
        fields = entry_schema.contract_fields(block)
        entry_schema.verify_sources(fields, root)
        sources = fields["source_hashes"]
        for name, expected in sources.items():
            if name in hashes and hashes[name] != expected:
                raise ValueError("The declarations bind different versions of one source.")
            hashes[name] = expected
    convention = design.get("table_convention", {})
    if "code_source_hashes" in convention:
        fields = {"source_hashes": convention["code_source_hashes"]}
        entry_schema.verify_sources(fields, root)
        for name, expected in fields["source_hashes"].items():
            if name in hashes and hashes[name] != expected:
                raise ValueError("The table code binds another source version.")
            hashes[name] = expected
    return hashes


def table_convention(design):
    """Accept entry families with existential parameters inside each state."""
    convention = design.get("table_convention")
    expected = {
        "entry_type": "(Z * iProp Sigma)",
        "pc_ownership": "instr_pre pc state supplies PC; entry predicates do not own PC",
        "existential_binders": "Each row's binders, in their listed order",
        "resource_application": "Apply resource_predicate to arguments in order",
        "code_persistence": "block_table_pre boxes the supplied code resource",
    }
    if not isinstance(convention, dict) or any(convention.get(key) != value
                                               for key, value in expected.items()):
        raise ValueError("The table convention is absent or differs from the approved convention.")
    code = convention.get("code_resource")
    sources = convention.get("code_source_hashes")
    if not isinstance(code, str) or not entry_schema.ROCQ_NAME.fullmatch(code):
        raise ValueError("The table code resource is not a fully qualified Rocq name.")
    if not isinstance(sources, dict) or not sources:
        raise ValueError("The table code resource has no bound source.")
    module = code.rsplit(".", 1)[0]
    if module.replace(".", "/") + ".v" not in sources:
        raise ValueError("The table code declaration has no bound source.")
    return convention


def signed(value, width):
    return value - (1 << width) if value & (1 << (width - 1)) else value


def control(row):
    """Decode targets from instruction bits; do not trust displacement metadata."""
    pc, word, size = address(row["pc"]), row["word"], row["size"]
    if size != 4 or not 0 <= word < 1 << 32 or word & 3 != 3:
        raise ValueError("The selected instruction is not a 32-bit instruction.")
    opcode, rd = word & 0x7f, (word >> 7) & 31
    if opcode == 0x63:
        immediate = (((word >> 31) & 1) << 12 | ((word >> 7) & 1) << 11 |
                     ((word >> 25) & 63) << 5 | ((word >> 8) & 15) << 1)
        displacement = signed(immediate, 13)
        operations = {0: ("eq", "ne"), 1: ("ne", "eq"),
                      4: ("s_lt", "s_ge"), 5: ("s_ge", "s_lt"),
                      6: ("u_lt", "u_ge"), 7: ("u_ge", "u_lt")}
        funct3 = (word >> 12) & 7
        if funct3 not in operations:
            raise ValueError("The branch has a reserved condition encoding.")
        register = lambda number: "0" if number == 0 else f"x{number}"
        left, right = register((word >> 15) & 31), register((word >> 20) & 31)
        targets = [pc + displacement, pc + size]
        guards = [{"op": op, "left": left, "right": right} for op in operations[funct3]]
        return "branch", targets, guards, displacement
    if opcode == 0x6f:
        immediate = (((word >> 31) & 1) << 20 | ((word >> 12) & 255) << 12 |
                     ((word >> 20) & 1) << 11 | ((word >> 21) & 1023) << 1)
        displacement = signed(immediate, 21)
        if rd != 0:
            raise ValueError("The selected region has an undeclared call.")
        return "jump", [pc + displacement], [{"op": "true"}], displacement
    if opcode == 0x67:
        if word != 0x8067:
            raise ValueError("The selected region has an unresolved indirect transfer.")
        return "return", [], [], 0
    kind = "load" if opcode == 0x03 else "store" if opcode == 0x23 else "plain"
    return kind, [pc + size], [{"op": "true"}], None


def structure(cfg, design):
    root = address(design["entry_pc"])
    functions = [function for function in cfg["functions"] if address(function["entry"]) == root]
    if len(functions) != 1:
        raise ValueError("The CFG must contain exactly one selected function.")
    function = functions[0]
    if function["name"] != design["function"]:
        raise ValueError("The CFG and design name different functions.")
    rows, blocks = function["rows"], function["blocks"]
    row_map = {address(row["pc"]): row for row in rows}
    block_map = {address(block["start"]): block for block in blocks}
    designs = {address(block["entry_pc"]): block for block in design["blocks"]}
    if len(row_map) != len(rows) or len(block_map) != len(blocks) or len(designs) != len(design["blocks"]):
        raise ValueError("The description repeats an instruction or block.")
    if set(block_map) != set(designs):
        raise ValueError("The CFG and design have different block entries.")
    end = address(function["end"])
    if address(design["end_pc_exclusive"]) != end:
        raise ValueError("The CFG and design have different function exits.")
    expected_pcs = set(range(root, end, 4))
    if set(row_map) != expected_pcs:
        raise ValueError("The instructions do not cover the selected function exactly.")
    owners, returns, edges, metadata_errors = Counter(), [], [], []
    instruction_edges = 0
    kinds = Counter()
    for pc, row in row_map.items():
        kind, successors, guards, immediate = control(row)
        kinds[kind] += 1
        if row.get("kind") != kind or set(map(address, row["successors"])) != set(successors):
            raise ValueError(f"Instruction control flow differs at {hex(pc)}.")
        if immediate is not None and row.get("imm") != immediate:
            metadata_errors.append({"pc": hex(pc), "stored_imm": row.get("imm"),
                                    "decoded_imm": immediate})
        instruction_edges += len(successors)
    for start, block in sorted(block_map.items()):
        stop = address(block["end"])
        pcs = [pc for pc in sorted(row_map) if start <= pc < stop]
        if not pcs or pcs[0] != start or pcs[-1] + row_map[pcs[-1]]["size"] != stop:
            raise ValueError("A block boundary splits or omits an instruction.")
        if start < root or stop > end or stop <= start:
            raise ValueError("A block leaves the selected function.")
        if address(designs[start]["end_pc_exclusive"]) != stop:
            raise ValueError("The design has a different block boundary.")
        owners.update(pcs)
        for pc in pcs[:-1]:
            if control(row_map[pc])[1] != [pc + row_map[pc]["size"]]:
                raise ValueError("A control transfer occurs inside a block.")
        tail = row_map[pcs[-1]]
        kind, successors, guards, _ = control(tail)
        if set(map(address, block["successors"])) != set(successors):
            raise ValueError("The block successors differ from its instruction word.")
        if set(map(address, designs[start]["successor_pcs"])) != set(successors):
            raise ValueError("The design omits or adds a block edge.")
        for target, guard in zip(successors, guards):
            if target not in block_map:
                raise ValueError("The block has an undeclared external exit.")
            edges.append({"source": hex(start), "instruction": hex(address(tail["pc"])),
                          "target": hex(target), "condition": guard})
        if kind == "return":
            clause = designs[start].get("return_clause", {})
            if address(clause.get("return_instruction_pc", -1)) != address(tail["pc"]):
                raise ValueError("The design omits or changes a return exit.")
            returns.append({"block": hex(start), "instruction": hex(address(tail["pc"])),
                            "word": hex(tail["word"]), "register": "x1"})
        elif not successors:
            raise ValueError("The block has no declared exit.")
    if set(owners) != set(row_map) or any(count != 1 for count in owners.values()):
        raise ValueError("An instruction belongs to zero or multiple blocks.")
    incoming = []
    entries = 0
    for target, block in designs.items():
        for edge in block["incoming_edges"]:
            if edge["from_block"] == "caller":
                if target != root or edge.get("kind") != "entry":
                    raise ValueError("The design has an unexpected caller entry.")
                entries += 1
            else:
                incoming.append({"source": hex(address(edge["from_block"])),
                                 "instruction": hex(address(edge["from_instruction"])),
                                 "target": hex(target), "condition": edge["path_condition"]})
    canonical = lambda values: Counter(json.dumps(value, sort_keys=True) for value in values)
    if entries != 1 or canonical(incoming) != canonical(edges):
        raise ValueError("The design incoming edges differ from the instruction words.")
    if sorted(map(address, function["returns"])) != sorted(address(row["instruction"]) for row in returns):
        raise ValueError("The CFG return inventory differs from the block exits.")
    if function["calls"]:
        raise ValueError("The selected function has undeclared call contracts.")
    active, visited, loop_edges = set(), set(), []
    def visit(pc):
        if pc in visited:
            return
        active.add(pc)
        for target in map(address, block_map[pc]["successors"]):
            if target in active:
                loop_edges.append({"source": hex(pc), "header": hex(target)})
            elif target not in visited:
                visit(target)
        active.remove(pc)
        visited.add(pc)
    visit(root)
    if visited != set(block_map):
        raise ValueError("The CFG has a block outside the selected entry graph.")
    counts = {"instructions": len(rows), "blocks": len(blocks), "instruction_edges": instruction_edges,
              "block_edges": len(edges), "returns": len(returns), "calls": 0,
              "conditional_branches": kinds["branch"], "loops": len(loop_edges)}
    for field, actual in (("instruction_count", len(rows)), ("block_count", len(blocks)),
                          ("conditional_branch_count", kinds["branch"]),
                          ("loop_count", len(loop_edges))):
        if design[field] != actual:
            raise ValueError(f"The design count differs: {field}.")
    return {"coverage": counts, "edges": edges, "returns": returns, "loop_edges": loop_edges,
            "displacement_metadata_discrepancies": metadata_errors,
            "missing_entry_definitions": [hex(pc) for pc, row in sorted(designs.items())
                                          if not row.get("entry_definition")]}


def bound_inputs(recipe_path, cfg_path, design_path):
    recipe = json.loads(recipe_path.read_text())
    cfg, design = json.loads(cfg_path.read_text()), json.loads(design_path.read_text())
    identity = recipe["artifact_identity"]
    binding = recipe["derived"]["cfg.json"]
    if cfg["schema"] != binding["schema_version"]:
        raise ValueError("The CFG schema version differs from the recipe.")
    if cfg["artifact_identity"] != identity or binding["artifact_identity"] != identity:
        raise ValueError("The CFG artifact identity differs from the recipe.")
    if digest(cfg_path) != recipe["artifacts"]["cfg.json"]:
        raise ValueError("The CFG hash differs from the recipe.")
    if design["hashes"]["selected_elf_sha256"] != recipe["elf_sha256"]:
        raise ValueError("The design has a different selected ELF.")
    inventory = recipe_path.parent / "inventory.json"
    if digest(inventory) != recipe["artifacts"]["inventory.json"] or digest(inventory) != design["hashes"]["inventory_sha256"]:
        raise ValueError("The design inventory hash differs from the bound inventory.")
    report = structure(cfg, design)
    hashes = {path_label(path): digest(path) for path in (recipe_path, cfg_path, design_path, inventory)}
    hashes.update(entry_source_hashes(design))
    hashes[path_label(Path(__file__))] = digest(__file__)
    return {"schema_version": 1, "artifact_identity": identity,
            "label": "Structural wiring coverage; no machine contract proof",
            "source_hashes": hashes,
            **report}


def render_table(design, report):
    """Render resource wiring; the completion interface still requires bodies.

    The caller must validate the approved table convention before rendering.
    This function introduces no body proof and no execution premise.
    """
    convention = table_convention(design)
    blocks = sorted(design["blocks"], key=lambda block: address(block["entry_pc"]))
    imports, states = {convention["code_resource"].rsplit(".", 1)[0]}, []
    for block in blocks:
        fields = entry_schema.contract_fields(block)
        if fields is None:
            raise ValueError("The block has no executable entry declaration.")
        predicate, entry = fields["resource_predicate"], fields["entry_definition"]
        imports.update((predicate.rsplit(".", 1)[0], entry.rsplit(".", 1)[0]))
        imports.update(entry_schema.source_module(path)
                       for path in fields["source_hashes"] if path.endswith(".v"))
        binders = block["binders"]
        typed = " ".join(f"({binder['name']} : {binder['type']})" for binder in binders)
        arguments = " ".join(f"({argument})" for argument in block["arguments"])
        application = f"{predicate} {arguments}".rstrip()
        body = f"∃ {typed}, {application}" if typed else application
        name = f"decodeItemState{address(block['entry_pc']):x}"
        states.append((block, name, body))
    lines = ["Require Import ZesuSsz.Automation.All.",
             "Require Import isla.riscv64.riscv64.",
             "From Coq Require Import List ZArith.",
             "Require Import ZesuSsz.Automation.BlockTable."]
    lines.extend(f"Require Import {module}." for module in sorted(imports))
    lines += ["Import ListNotations.", "Open Scope Z_scope.", "",
              "(* Generated resource wiring. No block-body proof is supplied. *)"]
    for path, sha in sorted(report.get("source_hashes", {}).items()):
        # The recipe binds generated output. Do not create a recipe/output hash cycle.
        if Path(path).name != "build-recipe.json":
            lines.append(f"(* Source: {path}; SHA-256: {sha}. *)")
    lines += ["", "Section decode_item_block_table.",
              "Context `{!islaG Sigma} `{!threadG}.", ""]
    for block, name, body in states:
        lines += [f"(* Entry: {block['entry_definition']}. Body proof: pending. *)",
                  f"Definition {name} : iProp Sigma :=", f"  ({body})%I.", ""]
    entries = ";\n   ".join(f"(0x{address(block['entry_pc']):x}, {name})"
                              for block, name, _ in states)
    lines += ["Definition decodeItemBlockTable : blockTable Sigma :=",
              "  {| block_table_code := " + convention["code_resource"] + ";",
              f"     block_table_entries := [{entries}] |}}.", "",
              "(* Completion requires the persistent code resource and every block body. *)",
              "Definition decodeItemBlockTable_complete :=",
              "  block_table_complete decodeItemBlockTable.", "",
              "End decode_item_block_table.", ""]
    edges = ";\n   ".join(f"({edge['source']}, {edge['target']})" for edge in report["edges"])
    returns = ";\n   ".join(f"({row['block']}, {row['instruction']})" for row in report["returns"])
    lines += ["Definition decodeItemBlockEdges : list (Z * Z) :=", f"  [{edges}].", "",
              "Definition decodeItemBlockReturns : list (Z * Z) :=", f"  [{returns}].", "",
              "Print Assumptions decodeItemBlockTable_complete.", ""]
    return "\n".join(lines)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--recipe", type=Path, default=ROOT / "build/stock-zisk/build-recipe.json")
    parser.add_argument("--cfg", type=Path, default=ROOT / "build/stock-zisk/cfg.json")
    parser.add_argument("--design", type=Path, default=ROOT / "ZesuSsz/Evidence/decode_item_block_design.json")
    parser.add_argument("--coverage", type=Path, required=True)
    parser.add_argument("--output", type=Path,
                        help="Write the Rocq table under the approved published convention.")
    args = parser.parse_args()
    report = bound_inputs(args.recipe, args.cfg, args.design)
    if args.output:
        design = json.loads(args.design.read_text())
        source = render_table(design, report)
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(source)
        report["table_convention"] = table_convention(design)
        report["generated_hashes"] = {path_label(args.output): digest(args.output)}
        report["proof_slots"] = [{"pc": block["entry_pc"], "entry_definition": block["entry_definition"],
                                  "resource_predicate": block["resource_predicate"], "proof_lemma": None}
                                 for block in design["blocks"]]
    args.coverage.parent.mkdir(parents=True, exist_ok=True)
    args.coverage.write_text(json.dumps(report, indent=2) + "\n")


if __name__ == "__main__":
    main()
