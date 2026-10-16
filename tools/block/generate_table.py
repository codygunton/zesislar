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
import re
import entry_schema
from function_names import FunctionNames, prefix_argument

ROOT = Path(__file__).resolve().parents[2]
PRODUCER_SHA_LINE = re.compile(
    r"^\(\* Source: tools/block/generate_table\.py; SHA-256: [0-9a-f]{64}\. \*\)\n", re.M)


def rocq_outputs_equal(before, after):
    """Compare every byte except one producer-SHA comment in each output."""
    def without_producer(source):
        matches, position, depth, quoted = [], 0, 0, False
        while position < len(source):
            match = PRODUCER_SHA_LINE.match(source, position) if not depth and not quoted else None
            if match:
                matches.append(match)
                position = match.end()
            elif quoted:
                if source.startswith('""', position):
                    position += 2
                elif source[position] == '"':
                    quoted = False
                    position += 1
                else:
                    position += 1
            elif source.startswith("(*", position):
                depth += 1
                position += 2
            elif depth and source.startswith("*)", position):
                depth -= 1
                position += 2
            elif not depth and source[position] == '"':
                quoted = True
                position += 1
            else:
                position += 1
        if len(matches) > 1:
            raise ValueError("The Rocq output contains duplicate producer-SHA comments.")
        if not matches:
            return 0, source
        match = matches[0]
        return 1, source[:match.start()] + source[match.end():]
    return without_producer(before) == without_producer(after)


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
        for edge in block.get("incoming_edges", []):
            if "resource_alternative" in edge:
                selected = entry_schema.edge_contract_fields(block, edge)
                entry_schema.verify_declarations(selected, root)
        sources = fields["source_hashes"]
        for name, expected in sources.items():
            if name in hashes and hashes[name] != expected:
                raise ValueError("The declarations bind different versions of one source.")
            hashes[name] = expected
    for call in call_contracts(design):
        fields = dict(entry_definition=call["contract_name"], resource_predicate=call["contract_name"],
                      source_hashes=call["source_hashes"])
        entry_schema.verify_sources(fields, root)
        entry_schema.verify_declarations(fields, root)
        for name, expected in fields["source_hashes"].items():
            if name in hashes and hashes[name] != expected:
                raise ValueError("The call contract binds another source version.")
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


def control(row, calls=None):
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
    if opcode == 0x67 and calls is not None and pc in calls:
        if rd != 1 or (word >> 12) & 7 or (word >> 15) & 31 != 1:
            raise ValueError("The resolved call is not a supported jalr x1 through x1.")
        return "call", [pc + size], [{"op": "true"}], signed(word >> 20, 12)
    if opcode == 0x67:
        if word != 0x8067:
            raise ValueError("The selected region has an unresolved indirect transfer.")
        return "return", [], [], 0
    kind = "load" if opcode == 0x03 else "store" if opcode == 0x23 else "plain"
    return kind, [pc + size], [{"op": "true"}], None


CALL_FIELDS = frozenset({"call_site_pc", "callee_pc", "return_site_pc", "contract_name",
                         "contract_arguments", "argument_type", "outcome_type", "source_hashes"})


def resolved_calls(function):
    """Resolve only an adjacent auipc/jalr pair and check the inventory twice."""
    rows = {address(row["pc"]): row for row in function["rows"]}
    result = {}
    for item in function["calls"]:
        if set(item) != {"pc", "target", "kind"} or item["kind"] != "call":
            raise ValueError("The call inventory has unsupported fields.")
        pc, target = address(item["pc"]), address(item["target"])
        if pc in result or pc not in rows or pc - 4 not in rows:
            raise ValueError("The call inventory repeats or omits an instruction.")
        row, prior = rows[pc], rows[pc - 4]
        word, upper = row["word"], prior["word"]
        if (row["size"] != 4 or prior["size"] != 4 or word & 0x7f != 0x67 or
                (word >> 7) & 31 != 1 or (word >> 15) & 31 != 1 or
                (word >> 12) & 7 or upper & 0x7f != 0x17 or (upper >> 7) & 31 != 1):
            raise ValueError("The call is not an adjacent auipc/jalr x1 pair.")
        decoded = ((pc - 4 + signed(upper & 0xfffff000, 32) +
                    signed(word >> 20, 12)) & ((1 << 64) - 1)) & ~1
        if target != decoded or address(row.get("target", -1)) != decoded:
            raise ValueError("The call target differs from the instruction words.")
        result[pc] = target
    if {pc for pc, row in rows.items() if row.get("kind") == "call"} != set(result):
        raise ValueError("The call rows differ from the call inventory.")
    return result


def call_contracts(design):
    """Keep each external contract explicit; an address never selects a contract."""
    calls = design.get("calls", [])
    if not isinstance(calls, list):
        raise ValueError("The call contracts are not an ordered list.")
    seen = set()
    for call in calls:
        if not isinstance(call, dict) or set(call) != CALL_FIELDS:
            raise ValueError("The call contract has unsupported fields.")
        pc = address(call["call_site_pc"])
        if pc in seen:
            raise ValueError("The call contract repeats an instruction.")
        seen.add(pc)
        for field in ("call_site_pc", "callee_pc", "return_site_pc"):
            value = call[field]
            if not isinstance(value, str) or not re.fullmatch(r"0x[0-9a-f]+", value):
                raise ValueError("The call address is not canonical hexadecimal.")
        if not isinstance(call["contract_name"], str) or not entry_schema.ROCQ_NAME.fullmatch(call["contract_name"]):
            raise ValueError("The call contract name is not fully qualified.")
        if not isinstance(call["contract_arguments"], list):
            raise ValueError("The call contract arguments are not an ordered list.")
        for value in call["contract_arguments"]:
            entry_schema.expression(value, "call contract argument")
        for field in ("argument_type", "outcome_type"):
            entry_schema.expression(call[field], field)
        # Reuse the exact source-path and hash schema used by block entries.
        entry_schema.contract_fields(dict(entry_definition=call["contract_name"],
            resource_predicate=call["contract_name"], binders=[], arguments=[],
            source_hashes=call["source_hashes"]))
    return calls


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
    call_targets = resolved_calls(function)
    declared_calls = {address(call["call_site_pc"]): call for call in call_contracts(design)}
    if set(declared_calls) != set(call_targets):
        raise ValueError("The selected function has undeclared call contracts.")
    for pc, call in declared_calls.items():
        if (address(call["callee_pc"]) != call_targets[pc] or
                address(call["return_site_pc"]) != pc + 4):
            raise ValueError("The call contract changes the callee or return site.")
    owners, returns, edges, metadata_errors = Counter(), [], [], []
    call_edges = []
    instruction_edges = 0
    kinds = Counter()
    for pc, row in row_map.items():
        kind, successors, guards, immediate = control(row, call_targets)
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
            if control(row_map[pc], call_targets)[0] == "call" or control(row_map[pc], call_targets)[1] != [pc + row_map[pc]["size"]]:
                raise ValueError("A control transfer occurs inside a block.")
        tail = row_map[pcs[-1]]
        kind, successors, guards, _ = control(tail, call_targets)
        if set(map(address, block["successors"])) != set(successors):
            raise ValueError("The block successors differ from its instruction word.")
        if set(map(address, designs[start]["successor_pcs"])) != set(successors):
            raise ValueError("The design omits or adds a block edge.")
        for target, guard in zip(successors, guards):
            if target not in block_map:
                raise ValueError("The block has an undeclared external exit.")
            edges.append({"source": hex(start), "instruction": hex(address(tail["pc"])),
                          "target": hex(target), "condition": guard})
        if kind == "call":
            call = declared_calls[address(tail["pc"])]
            call_edges.append({"source": hex(start), "instruction": call["call_site_pc"],
                               "callee_pc": call["callee_pc"], "return_site_pc": call["return_site_pc"],
                               "contract_name": call["contract_name"]})
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
    alternatives = {}
    entries = 0
    for target, block in designs.items():
        for edge in block["incoming_edges"]:
            if "resource_alternative" in edge:
                fields = entry_schema.edge_contract_fields(block, edge)
            if edge["from_block"] == "caller":
                if target != root or edge.get("kind") != "entry":
                    raise ValueError("The design has an unexpected caller entry.")
                entries += 1
            else:
                row = {"source": hex(address(edge["from_block"])),
                       "instruction": hex(address(edge["from_instruction"])),
                       "target": hex(target), "condition": edge["path_condition"]}
                incoming.append(row)
                if "resource_alternative" in edge:
                    alternatives[json.dumps(row, sort_keys=True)] = fields["entry_definition"]
    canonical = lambda values: Counter(json.dumps(value, sort_keys=True) for value in values)
    if entries != 1 or canonical(incoming) != canonical(edges):
        raise ValueError("The design incoming edges differ from the instruction words.")
    for edge in edges:
        selected = alternatives.get(json.dumps(edge, sort_keys=True))
        if selected is not None:
            edge["resource_alternative"] = selected
    if sorted(map(address, function["returns"])) != sorted(address(row["instruction"]) for row in returns):
        raise ValueError("The CFG return inventory differs from the block exits.")
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
              "block_edges": len(edges), "returns": len(returns), "calls": len(call_edges),
              "conditional_branches": kinds["branch"], "loops": len(loop_edges)}
    for field, actual in (("instruction_count", len(rows)), ("block_count", len(blocks)),
                          ("conditional_branch_count", kinds["branch"]),
                          ("loop_count", len(loop_edges))):
        if design[field] != actual:
            raise ValueError(f"The design count differs: {field}.")
    return {**({"calls": call_edges} if call_edges else {}),
            "coverage": counts, "edges": edges, "returns": returns, "loop_edges": loop_edges,
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


def render_table(design, report, *, name_prefix="decodeItem"):
    """Render resource wiring; the completion interface still requires bodies.

    The caller must validate the approved table convention before rendering.
    This function introduces no body proof and no execution premise.
    """
    names = FunctionNames(name_prefix)
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
        name = names.state(address(block['entry_pc']))
        states.append((block, name, body))
    calls = call_contracts(design)
    if calls:
        imports.add("ZesuSsz.Contracts.Level1")
        for call in calls:
            imports.update(entry_schema.source_module(path) for path in call["source_hashes"] if path.endswith(".v"))
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
    lines += ["", f"Section {names.filename}_block_table.",
              "Context `{!islaG Sigma} `{!threadG}.", ""]
    for block, name, body in states:
        lines += [f"(* Entry: {block['entry_definition']}. Body proof: pending. *)",
                  f"Definition {name} : iProp Sigma :=", f"  ({body})%I.", ""]
    call_premises = []
    for call in calls:
        name = f"{names.prefix}CallState{address(call['call_site_pc']):x}"
        args_type, out_type = call["argument_type"], call["outcome_type"]
        model = call["contract_name"] + "".join(f" ({arg})" for arg in call["contract_arguments"])
        lines += [f"(* External contract: {call['contract_name']}. Installation proof: pending. *)",
                  f"Definition {name} : iProp Sigma :=",
                  f"  let model := {model} in",
                  f"  let resources := islarisContractResources ({args_type}) ({out_type}) model Sigma _ _ in",
                  f"  (∃ args : {args_type},",
                  f"    islarisEntry ({args_type}) ({out_type}) resources args ∗",
                  f"    instr_pre {call['return_site_pc']} (∃ outcome : {out_type},",
                  f"      ⌜islarisContractAllows ({args_type}) ({out_type}) model args outcome⌝ ∗",
                  f"      islarisExit ({args_type}) ({out_type}) resources args outcome))%I.", ""]
        call_premises.append(f"□ instr_pre {call['callee_pc']} {name}")
    code = convention["code_resource"]
    if call_premises:
        code = "(" + " ∗ ".join([code] + call_premises) + ")%I"
    entries = ";\n   ".join(f"(0x{address(block['entry_pc']):x}, {name})"
                              for block, name, _ in states)
    lines += [f"Definition {names.table} : blockTable Sigma :=",
              "  {| block_table_code := " + code + ";",
              f"     block_table_entries := [{entries}] |}}.", "",
              "(* Completion requires the persistent code resource and every block body. *)",
              f"Definition {names.table}_complete :=",
              f"  block_table_complete {names.table}.", "",
              f"End {names.filename}_block_table.", ""]
    edges = ";\n   ".join(f"({edge['source']}, {edge['target']})" for edge in report["edges"])
    returns = ";\n   ".join(f"({row['block']}, {row['instruction']})" for row in report["returns"])
    lines += [f"Definition {names.prefix}BlockEdges : list (Z * Z) :=", f"  [{edges}].", "",
              f"Definition {names.prefix}BlockReturns : list (Z * Z) :=", f"  [{returns}].", "",
              f"Print Assumptions {names.table}_complete.", ""]
    return "\n".join(lines)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--function", type=prefix_argument, default="decodeItem")
    parser.add_argument("--recipe", type=Path, default=ROOT / "build/stock-zisk/build-recipe.json")
    parser.add_argument("--cfg", type=Path, default=ROOT / "build/stock-zisk/cfg.json")
    parser.add_argument("--design", type=Path)
    parser.add_argument("--coverage", type=Path, required=True)
    parser.add_argument("--output", type=Path,
                        help="Write the Rocq table under the approved published convention.")
    parser.add_argument("--check", action="store_true", help="Check existing output bytes without writing files.")
    args = parser.parse_args()
    names = FunctionNames(args.function)
    args.design = args.design or ROOT / f"ZesuSsz/Evidence/{names.filename}_block_design.json"
    report = bound_inputs(args.recipe, args.cfg, args.design)
    if args.output:
        design = json.loads(args.design.read_text())
        source = render_table(design, report, name_prefix=args.function)
        if args.check:
            if not args.output.is_file() or not rocq_outputs_equal(
                    args.output.read_bytes().decode("utf-8"), source):
                raise ValueError("The generated Rocq table is stale.")
        else:
            args.output.parent.mkdir(parents=True, exist_ok=True)
            args.output.write_text(source)
        report["table_convention"] = table_convention(design)
        report["generated_hashes"] = {path_label(args.output): digest(args.output)}
        report["proof_slots"] = [{"pc": block["entry_pc"], "entry_definition": block["entry_definition"],
                                  "resource_predicate": block["resource_predicate"], "proof_lemma": None}
                                 for block in design["blocks"]]
    rendered = json.dumps(report, indent=2) + "\n"
    if args.check:
        if not args.coverage.is_file() or args.coverage.read_text() != rendered:
            raise ValueError("The generated table metadata is stale.")
    else:
        args.coverage.parent.mkdir(parents=True, exist_ok=True)
        args.coverage.write_text(rendered)


if __name__ == "__main__":
    main()
