#!/usr/bin/env python3
"""Emit production proof sources for measured native and transfer closures.

The emitted inventory is not a certificate. Dune and Rocq must check each
module against the current production dependencies before promotion.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import re
from function_names import FunctionNames, prefix_argument


DIRECTORY = Path("ZesuSsz/Proofs/DecodeItem/Auto")
REQUIRED_IMPORTS = (
    "ZesuSsz.Automation.All",
    "ZesuSsz.Automation.Approved",
    "ZesuSsz.Compliance.DecodeItemHints",
)
IDENTIFIER = r"[A-Za-z_][A-Za-z0-9_']*"


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def statement(source, lemma):
    """Return the exact prepared declaration without separator whitespace."""
    if not re.fullmatch(IDENTIFIER, lemma):
        raise ValueError("The production lemma name is invalid.")
    matches = list(re.finditer(r"^Lemma " + re.escape(lemma) + r"\b", source, re.M))
    if len(matches) != 1:
        raise ValueError("The source lacks one named theorem declaration.")
    start = matches[0].start()
    end = source.index("\nProof.", start)
    return source[start:end]


def module_name(rendered, kind, *, name_prefix="decodeItem"):
    names = FunctionNames(name_prefix)
    if kind in {"native", "raw_statement"}:
        pc = rendered["entry_pc"]
        if not re.fullmatch(r"0x[0-9a-f]+", pc):
            raise ValueError("The production entry address is invalid.")
        stem = "Block" + pc[2:]
    elif kind == "adapter":
        lemma = rendered["lemma"]
        if not lemma.startswith(names.prefix) or not lemma.endswith("_automatic"):
            raise ValueError("The transfer adapter lacks its prepared name.")
        stem = lemma[len(names.prefix):-len("_automatic")]
    else:
        raise ValueError("The production obligation kind is invalid.")
    if not re.fullmatch(IDENTIFIER, stem):
        raise ValueError("The production module name is invalid.")
    return names.proofs + ".Auto." + stem


def object_path(module):
    """Map a logical module to its exact Coq object path."""
    return Path(module.replace(".", "/")).with_suffix(".vo")


RAW_STATEMENT_SEPARATOR = "(* Transport separator outside the protected statement. *)\n"


def raw_statement_source(rendered):
    """Transport one hash-bound declaration without changing its bytes.

    A comment starts immediately after the protected interval.  In particular,
    a declaration without a final newline gets no synthetic newline inside
    that interval.  The unchanged native statement reader stops before the
    comment.  An existing final newline remains part of the protected bytes.
    """
    from check_data_only_lemmas import rocq_commands

    prefix, declaration = rendered["source"], rendered["statement"]
    if hashlib.sha256(prefix.encode()).hexdigest() != rendered["source_sha256"]:
        raise ValueError("The raw statement source prefix changed.")
    if hashlib.sha256(declaration.encode()).hexdigest() != rendered["statement_sha256"]:
        raise ValueError("The raw statement bytes changed.")
    lemma = rendered["lemma"]
    if not re.fullmatch(IDENTIFIER, lemma):
        raise ValueError("The raw statement lemma name is invalid.")
    commands = rocq_commands(declaration)
    if (len(commands) != 1 or [word for word, _ in commands[0]][:2] != ["Lemma", lemma]
            or not declaration.startswith("Lemma " + lemma)
            or not (declaration.endswith(".") or declaration.endswith(".\n"))
            or "\r" in declaration):
        raise ValueError("The raw statement requires one exact terminated lemma.")
    if not prefix.startswith("Require Import ZesuSsz.Automation.All.\n"):
        raise ValueError("The raw statement prefix lacks the production import.")
    forbidden = {"Proof", "Qed", "Defined", "Admitted", "Abort", "Axiom",
                 "Parameter", "Lemma", "Theorem", "Goal", "Ltac", "Ltac2", "ltac", "ltac2", "admit"}
    if any(word in forbidden for command in rocq_commands(prefix) for word, _ in command):
        raise ValueError("The raw statement prefix contains a proof command.")
    if re.search(r"\b(?:RuleScratchRules|AllLegacy|Ltac2?)\b", prefix):
        raise ValueError("The raw statement prefix is not plain production stock.")
    # Keep the source prefix, imports, declaration, and source scopes literal.
    before = prefix + "\n"
    source = (before + declaration + RAW_STATEMENT_SEPARATOR +
              "Proof.\n  zesu_block.\nQed.\n\nPrint Assumptions " + lemma + ".\n")
    interval = source.encode()[len(before.encode()):len(before.encode()) + len(declaration.encode())]
    if hashlib.sha256(interval).hexdigest() != rendered["statement_sha256"]:
        raise ValueError("The transported raw statement changed.")
    return source


def render(rendered, kind, *, name_prefix="decodeItem"):
    """Preserve the declaration and use only the production block tactic."""
    if kind == "raw_statement":
        return raw_statement_source(rendered)
    names = FunctionNames(name_prefix)
    required_imports = (*REQUIRED_IMPORTS[:2], names.hints)
    source, lemma = rendered["source"], rendered["lemma"]
    declaration = statement(source, lemma)
    if hashlib.sha256(declaration.encode()).hexdigest() != rendered["statement_sha256"]:
        raise ValueError("The prepared production statement changed.")
    prefix = source[:source.index(declaration)]
    body, tail = source[source.index(declaration) + len(declaration) +
                        len("\nProof."):].split("\nQed.", 1)
    if body.strip() != "try zesu_block.":
        raise ValueError("The prepared body contains an unsupported proof step.")
    if tail.strip() != "Print Assumptions " + lemma + ".":
        raise ValueError("The prepared source lacks its exact assumption check.")
    imports = []
    for group in re.findall(r"^Require Import ([^\n]+)\.$", prefix, re.M):
        for name in group.split():
            if name == "Boundary" or name.endswith(".Boundary"):
                raise ValueError("A production proof cannot import a frozen Boundary.")
            if (name not in required_imports and
                    not name.startswith("ZesuSsz.Automation.Switches.") and
                    name not in imports):
                imports.append(name)
    from_imports = list(dict.fromkeys(re.findall(
        r"^From [^\n]+ Require Import [^\n]+\.$", prefix, re.M)))
    settings = list(dict.fromkeys(re.findall(
        r"^(?:Open Scope [^\n]+|Import [^\n]+)\.$", prefix, re.M)))
    if any(re.search(r"\bBoundary\b", line) for line in [*from_imports, *settings]):
        raise ValueError("A production proof cannot import a frozen Boundary.")
    local = ""
    if kind == "native":
        name = "DesignedEntry_" + rendered["entry_pc"][2:]
        start = prefix.index("Definition " + name)
        end_marker = "Global Typeclasses Opaque " + name + "."
        end = prefix.index(end_marker, start) + len(end_marker)
        local = prefix[start:end] + "\n\n"
        if "Global Instance : LithiumUnfold (@" + name + ") := I." not in local:
            raise ValueError("The prepared entry lacks its unfolding instance.")
    elif kind != "adapter":
        raise ValueError("The production obligation kind is invalid.")
    result = "".join("Require Import " + name + ".\n"
                     for name in [*required_imports, *imports])
    result += "".join(line + "\n" for line in [*from_imports, *settings])
    result += "\n" + local + declaration + "\nProof.\n  zesu_block.\nQed.\n\n"
    result += "Print Assumptions " + lemma + ".\n"
    if statement(result, lemma) != declaration:
        raise ValueError("The production declaration differs from its preparation.")
    return result


def emit(rendered, kind, workspace, *, name_prefix="decodeItem"):
    """Write one current-source module without reading a frozen object."""
    module = module_name(rendered, kind, name_prefix=name_prefix)
    relative = object_path(module).with_suffix(".v")
    if relative.parent != Path(FunctionNames(name_prefix).proofs.replace(".", "/")) / "Auto":
        raise ValueError("The production module leaves its approved directory.")
    source = render(rendered, kind, name_prefix=name_prefix)
    workspace = Path(workspace).resolve()
    path = workspace / relative
    if not path.resolve().is_relative_to(workspace):
        raise ValueError("The production source path leaves its workspace.")
    if path.exists() and path.read_text() != source:
        raise ValueError("An existing production module has different source.")
    path.parent.mkdir(parents=True, exist_ok=True)
    if not path.exists():
        if kind == "raw_statement":
            path.write_bytes(source.encode())
        else:
            path.write_text(source)
    result = {
        "module": module,
        "lemma": module + "." + rendered["lemma"],
        "source": str(relative),
        "source_sha256": digest(path),
        "statement_sha256": rendered["statement_sha256"],
        "prepared_source_sha256": hashlib.sha256(rendered["source"].encode()).hexdigest(),
        "kind": kind,
        "dune_target": str(object_path(module)),
    }
    if kind == "raw_statement":
        start = len((rendered["source"] + "\n").encode())
        result["protected_statement"] = {
            "start_byte": start,
            "end_byte": start + len(rendered["statement"].encode()),
            "sha256": rendered["statement_sha256"],
            "trailing_newline": rendered["statement"].endswith("\n"),
            "separator_outside_interval": RAW_STATEMENT_SEPARATOR,
        }
    return result


def emit_pass(report, jobs, workspace, *, name_prefix="decodeItem"):
    """Select measured closures while preserving each prepared declaration."""
    workspace = Path(workspace).resolve()
    by_id = {job["id"]: job for job in jobs}
    if len(by_id) != len(jobs):
        raise ValueError("The production jobs repeat an obligation.")
    prepared = []
    selected = set()
    for row in report["rows"]:
        if row["outcome"] not in ("native-closure", "adapter-closure"):
            continue
        if row["id"] in selected:
            raise ValueError("The closure report repeats an obligation.")
        selected.add(row["id"])
        kind = "native" if row["outcome"] == "native-closure" else "adapter"
        job = by_id[row["id"]]
        debts = row.get("inherited_debts")
        if (row.get("kind") != kind or job["kind"] != kind or
                row.get("exit_code") != 0 or row.get("limit") is not None or
                row.get("assumptions_verified") is not True or
                not isinstance(debts, dict) or any(debts.values())):
            raise ValueError("The selected historical closure lacks debt-free evidence.")
        source_path = Path(job["source"])
        if digest(source_path) != job["source_sha256"]:
            raise ValueError("The prepared source hash differs.")
        if job["statement_sha256"] != row["statement_sha256"]:
            raise ValueError("The closure binds a different prepared statement.")
        rendered = {**job, "source": source_path.read_text()}
        module = module_name(rendered, kind, name_prefix=name_prefix)
        source = render(rendered, kind, name_prefix=name_prefix)
        target = workspace / object_path(module).with_suffix(".v")
        if not target.resolve().is_relative_to(workspace):
            raise ValueError("The production source path leaves its workspace.")
        if target.exists() and target.read_text() != source:
            raise ValueError("An existing production module has different source.")
        prepared.append((rendered, kind))
    modules = [module_name(rendered, kind, name_prefix=name_prefix) for rendered, kind in prepared]
    if len(modules) != len(set(modules)):
        raise ValueError("The production obligations collide on a module name.")
    return [emit(rendered, kind, workspace, name_prefix=name_prefix) for rendered, kind in prepared]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--function", type=prefix_argument, default="decodeItem")
    parser.add_argument("--pass-report", type=Path, required=True)
    parser.add_argument("--pass-report-sha256", required=True)
    parser.add_argument("--jobs", type=Path, required=True)
    parser.add_argument("--jobs-sha256", required=True)
    parser.add_argument("--workspace", type=Path, required=True)
    parser.add_argument("--inventory", type=Path, required=True)
    args = parser.parse_args()
    for path, expected in [(args.pass_report, args.pass_report_sha256),
                           (args.jobs, args.jobs_sha256)]:
        if digest(path) != expected:
            raise ValueError("The reviewed production input hash differs.")
    report = json.loads(args.pass_report.read_text())
    rows = emit_pass(report, json.loads(args.jobs.read_text()), args.workspace, name_prefix=args.function)
    inventory = {
        "schema_version": 1,
        "scope": "Production source inventory. This file is not proof evidence.",
        "historical_root": report["root"],
        "historical_report_sha256": args.pass_report_sha256,
        "historical_jobs_sha256": args.jobs_sha256,
        "required_imports": [*REQUIRED_IMPORTS[:2], FunctionNames(args.function).hints],
        "modules": rows,
    }
    args.inventory.parent.mkdir(parents=True, exist_ok=True)
    args.inventory.write_text(json.dumps(inventory, sort_keys=True, indent=2) + "\n")
    print(json.dumps({"modules": len(rows), "inventory": str(args.inventory),
                      "sha256": digest(args.inventory)}))


if __name__ == "__main__":
    main()
