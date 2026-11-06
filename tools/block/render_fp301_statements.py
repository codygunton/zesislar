"""Render FP301 return packages and caller statements from authenticated inputs."""

import argparse
import hashlib
import json
from pathlib import Path

from production_modules import statement as caller_statement
from render_support import definition_introduction_source, unfold_declaration
from return_exit import add_return_precondition, return_blocks, return_package


def binding(path):
    path = Path(path)
    return {"path": str(path), "sha256": hashlib.sha256(path.read_bytes()).hexdigest()}


def read_bound(row):
    path = Path(row["path"])
    if binding(path) != row:
        raise ValueError("A return-renderer input changed: " + str(path))
    return path.read_text()


def render_caller(source):
    """Keep the canonical caller and select the second automation entry point."""
    if "::=" in source or "Ltac " in source:
        raise ValueError("A canonical caller cannot contain tactic overrides.")
    if source.count("Require Import ZesuSsz.Automation.All.") < 1:
        raise ValueError("A canonical caller lacks its automation import.")
    if source.count("  zesu_block.\nQed.") != 1:
        raise ValueError("A canonical caller lacks its plain block proof.")
    return source.replace("Require Import ZesuSsz.Automation.All.",
                          "Require Import ZesuSsz.Automation2.All.").replace(
                              "  zesu_block.\nQed.", "  zesu_block2.\nQed.")


def render(inputs, output):
    design = json.loads(read_bound(inputs["design"]))
    callers = json.loads(read_bound(inputs["callers"]))
    declarations = json.loads(read_bound(inputs["declarations"]))
    source = read_bound(inputs["return_source"])
    closed_cases = inputs["closed_cases"]
    if len(closed_cases) != 10 or len(set(closed_cases)) != 10:
        raise ValueError("The preservation gate needs the ten distinct closed cases.")
    if not set(closed_cases) <= {row["case"] for row in callers["rows"]}:
        raise ValueError("A closed case has no authenticated caller statement.")
    returns = return_blocks(design)
    parameters = [
        {"name": "args", "type": "DecodeItemArgs"},
        {"name": "returnAddress", "type": "Z"},
        {"name": "K", "type": "iProp Sigma"},
    ]
    symbol = "fp_machineReturn"
    definition, provenance = return_package(
        source, inputs["return_symbol"], symbol, parameters
    )
    entries = {row["pc"]: row for row in declarations["cases"]}
    prepared = []
    for row in callers["rows"]:
        text = read_bound(row["caller"])
        pc = int("800d" + row["case"], 16)
        name = "DesignedBoundary_" + format(pc, "x")
        original = caller_statement(text, name)
        application = (
            "ZesuSsz.Generated.DecodeItem.FP301.FunctionReturnEntries."
            + symbol + " args returnAddress K"
        )
        changed = pc in returns
        rendered = (
            add_return_precondition(original, "returnAddress", application)
            if changed else original
        )
        if row["case"] in inputs["closed_cases"] and rendered != original:
            raise ValueError("A closed generated statement would change: " + row["case"])
        if hex(pc) not in entries:
            raise ValueError("A caller lacks its rendered FP301 entry: " + hex(pc))
        prepared.append((row, original, rendered, changed))

    # Validate every declaration binding before creating an output directory.
    for row in declarations["sources"]:
        read_bound(row)
    output = Path(output)
    output.mkdir(exist_ok=False)
    directory = output / "sources/ZesuSsz/Generated/DecodeItem/FP301"
    directory.mkdir(parents=True)
    header = """(* Generated from the authenticated function-return resource package. *)
Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith NArith.NArith.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Require Import ZesuSsz.Contracts.RlpDecodeItem.
Require ZesuSsz.Automation.Hooks.
Local Open Scope Z_scope.
"""
    entry = directory / "FunctionReturnEntries.v"
    entry.write_text(header + "\n" + definition)
    structural = directory / "FunctionReturnStructural.v"
    structural.write_text(
        header
        + "Require Import ZesuSsz.Generated.DecodeItem.FP301.FunctionReturnEntries.\n"
        + unfold_declaration(symbol, instance_name=symbol + "_unfold", locality="export")
        + definition_introduction_source(definition, symbol)
    )
    statements = output / "statements"
    statements.mkdir()
    rows = []
    caller_directory = output / "callers"
    caller_directory.mkdir()
    for row, original, rendered, changed in prepared:
        path = statements / (row["case"] + ".vpart")
        path.write_text(rendered)
        caller_source = read_bound(row["caller"]).replace(original, rendered, 1)
        if changed:
            caller_source = ("Require Import ZesuSsz.Generated.DecodeItem.FP301.FunctionReturnStructural.\n"
                             + caller_source)
        caller = caller_directory / ("Caller" + row["case"] + ".v")
        caller.write_text(render_caller(caller_source))
        rows.append({
            "caller": binding(caller),
            "case": row["case"],
            "original_caller": row["caller"],
            "original_statement_sha256": hashlib.sha256(original.encode()).hexdigest(),
            "statement": binding(path),
            "changed": changed,
            "exit_kind": "function_return" if changed else "successor",
            "additional_imports": [
                "ZesuSsz.Generated.DecodeItem.FP301.FunctionReturnStructural"
            ] if changed else [],
        })
    result = {
        "status": "SOURCE_DECLARATIONS_ONLY",
        "inputs": inputs,
        "function_return_blocks": [hex(pc) for pc in sorted(returns)],
        "return_preconditions": [
            {
                "entry_pc": hex(pc),
                "return_instruction_pc": returns[pc]["return_clause"]["return_instruction_pc"],
                "address": "returnAddress",
                "package": "ZesuSsz.Generated.DecodeItem.FP301.FunctionReturnEntries."
                           + symbol + " args returnAddress K",
            }
            for pc in sorted(returns)
        ],
        "changed_blocks": [row["case"] for row in rows if row["changed"]],
        "closed_cases_unchanged": inputs["closed_cases"],
        "return_source_projection": provenance,
        "sources": [binding(entry), binding(structural)],
        "statements": rows,
        "existing_FP301_declarations_unchanged": declarations["sources"],
        "function_level_contract_changed": False,
        "proof_scripts_emitted": False,
    }
    (output / "RESULT.json").write_text(json.dumps(result, indent=2) + "\n")
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--inputs", type=Path, required=True)
    parser.add_argument("--inputs-sha256", required=True)
    parser.add_argument("--output", type=Path, required=True)
    options = parser.parse_args()
    inputs = json.loads(read_bound({
        "path": str(options.inputs), "sha256": options.inputs_sha256
    }))
    result = render(inputs, options.output)
    print(json.dumps({"changed_blocks": result["changed_blocks"],
                      "closed_cases_unchanged": result["closed_cases_unchanged"]}))


if __name__ == "__main__":
    main()
