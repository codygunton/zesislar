#!/usr/bin/env python3
"""Compare one automation switch on identical scratch contract statements.

This tool writes private evidence and a metrics fragment. It does not update
the coordinator's metrics or certify a production proof checkpoint.
"""

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import sys
import subprocess

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from coqc_recipe import snapshot_recipe
from residual.modules import parse_module

import chain_goals
import coqc_primary

IDENTIFIER = r"[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*"


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def save(path, value):
    Path(path).write_text(json.dumps(value, indent=2) + "\n")


def without_comments(text):
    """Blank nested comments without changing source offsets or line numbers."""
    result = list(text)
    depth, index, quoted = 0, 0, False
    while index < len(text):
        if not depth and text[index] == '"':
            if quoted and text[index:index + 2] == '""':
                index += 2
                continue
            quoted = not quoted
        if not quoted and text[index:index + 2] == "(*":
            depth += 1
            result[index:index + 2] = "  "
            index += 2
        elif depth and text[index:index + 2] == "*)":
            depth -= 1
            result[index:index + 2] = "  "
            index += 2
        else:
            if depth and text[index] != "\n":
                result[index] = " "
            index += 1
    if depth:
        raise ValueError("The source has an unclosed comment.")
    return "".join(result)


def imported_modules(text):
    text = without_comments(text)
    pattern = r"^(?:From\s+([\w.]+)\s+)?Require\s+(?:Import|Export)\s+([\w.\s]+?)\.\s*$"
    for match in re.finditer(pattern, text, re.M):
        prefix, names = match.groups()
        for name in names.split():
            yield (prefix + "." if prefix else "") + name


def switch_instances(workspace, prefix, switch):
    """Find named instances in the source's project import closure."""
    if not re.fullmatch(IDENTIFIER, switch):
        raise ValueError("The switch class is not an identifier.")
    visited, instances = set(), []
    short = switch.rsplit(".", 1)[-1]

    def visit(text, module):
        for name in imported_modules(text):
            if name in visited:
                continue
            visited.add(name)
            path = workspace / (name.replace(".", "/") + ".v")
            if path.is_file():
                visit(path.read_text(), name)
        pattern = (r"\bInstance\s+(" + IDENTIFIER + r")\s*:\s*("
                   + IDENTIFIER + r")\s*:=\s*(?:I|\{\s*\})\s*\.")
        for match in re.finditer(pattern, without_comments(text)):
            name, cls = match.groups()
            if cls == switch or cls.rsplit(".", 1)[-1] == short:
                qualified = module + "." + name if module else name
                if qualified not in instances:
                    instances.append(qualified)

    visit(prefix, "")
    return instances


def prepare(module, workspace, switch, lemma=None, keyed_lemma=None):
    """Replace only the selected proof and add equal diagnostic instrumentation."""
    if keyed_lemma and not re.fullmatch(IDENTIFIER, keyed_lemma):
        raise ValueError("The keyed lemma must be one qualified identifier.")
    source = module.read_text()
    proofs = parse_module(module)
    selected = [p for p in proofs if p.name == lemma] if lemma else [
        p for p in proofs if p.name.startswith("DesignedBoundary_")]
    if len(selected) != 1:
        raise ValueError("The main proof selection is missing or ambiguous.")
    proof = selected[0]
    if proof.inline:
        raise ValueError("The main proof must have a separate Proof line.")
    lines = source.splitlines(keepends=True)
    prefix = "".join(lines[:proof.declaration_line])
    statement = "".join(lines[proof.declaration_line:proof.proof_line])
    opener = lines[proof.proof_line]
    tail = "".join(lines[proof.terminator_line:])
    if without_comments(lines[proof.terminator_line]).strip() != "Qed.":
        raise ValueError("The selected proof must end with Qed.")
    instances = switch_instances(workspace, prefix, switch)
    imports = list(imported_modules(prefix))
    copies, arm_instances = {}, {}
    for enabled in (False, True):
        arm = "rule_on" if enabled else "rule_off"
        removals = [] if enabled else instances
        removal = "".join("Remove Hints " + name + " : typeclass_instances.\n"
                          for name in removals)
        local = "#[local] Instance : " + switch + " := I."
        additions = [local] if enabled and not instances else []
        instance = "".join(line + "\n" for line in additions)
        arm_instances[arm] = {"removals": removals, "local_additions": additions,
                              "expected_enabled": enabled}
        assertion = ("" if enabled else "Fail ") + (
            "Definition rule_compare_switch_probe : " + switch
            + " := ltac:(typeclasses eauto).\n")
        body = "  zesu_block.\n"
        if keyed_lemma:
            body += ('  all: idtac "RULE-COMPARE-AUTOMATIC-RETURNED".\n'
                     '  all: idtac "RULE-COMPARE-KEYED-BEGIN".\n'
                     "  apply " + keyed_lemma + ".\n"
                     '  all: idtac "RULE-COMPARE-KEYED-RETURNED".\n')
        diagnostic = ('  all: (chain_print_goal "active"; idtac "CHAIN-GOAL-END").\n'
                      '  Unshelve.\n'
                      '  all: idtac "RULE-COMPARE-RETURNED".\n'
                      '  all: (chain_print_goal "shelved"; idtac "CHAIN-GOAL-END").\n'
                      '  Show Existentials.\n')
        result = (prefix + removal + instance + assertion + chain_goals.RECORDER
                  + "\n" + statement + opener + '  idtac "RULE-COMPARE-BEGIN".\n'
                  + body + '  all: idtac "RULE-COMPARE-RETURNED".\n'
                  + diagnostic + tail)
        if "Print Assumptions " + proof.name + "." not in tail:
            result += "\nPrint Assumptions " + proof.name + ".\n"
        copies[arm] = result
        assert list(imported_modules(result)) == imports
    return {"copies": copies, "lemma": proof.name, "statement": statement,
            "statement_sha256": hashlib.sha256(statement.encode()).hexdigest(),
            "existing_instances": instances, "arm_instances": arm_instances,
            "imports": imports,
            "original_hand_lines": len(proof.hand_lines)}


def residual_class(goal):
    conclusion = goal["conclusion"]
    if re.search(r"FindMemMapsTo|MKArray|mem_mapsto|↦ₘ", conclusion):
        return "memory"
    if re.search(r"FindInstrKind|instr_pre", conclusion):
        return "handoff"
    if re.search(r"∃|exists|\?[A-Za-z_]", conclusion):
        return "existential"
    return "other"


def decode_goals(output):
    """Read both observation points using complete conclusion delimiters."""
    starts = list(re.finditer(r'CHAIN-GOAL-BEGIN\s+"?(active|shelved)"?\b', output))
    records = []
    for index, start in enumerate(starts):
        end = starts[index + 1].start() if index + 1 < len(starts) else len(output)
        segment = output[start.start():end]
        conclusions = list(re.finditer(
            r'"?CHAIN-GOAL-CONCLUSION"?\s+.*?\s*CHAIN-FIELD-END', segment, re.S))
        if len(conclusions) != 1:
            raise ValueError("The printed goal lacks one terminated conclusion.")
        normalized = segment[:conclusions[0].end()] + "\nCHAIN-GOAL-END\n"
        goals = chain_goals.parse_goals(normalized, allow_local_definitions=True)
        for goal in goals:
            # This second observation includes surviving original active goals.
            if goal["phase"] == "shelved":
                goal["phase"] = "post-unshelve"
        records.extend(goals)
    return records


def classify(exit_code, output, compiler, lemma=None):
    """Require returned goals and an incomplete Qed error for a residual result."""
    result = {"first_residual": None, "goals": None}
    if compiler is None:
        return {**result, "outcome": "setup-error"}
    if compiler.get("limit") or compiler.get("policy_error"):
        return {**result, "outcome": "runtime-error"}
    if "RULE-COMPARE-BEGIN" not in output:
        return {**result, "outcome": "setup-error"}
    if not exit_code and compiler.get("compiled_object"):
        assumptions = coqc_primary.assumptions_result(output, "")
        if assumptions["verified"]:
            return {**result, "outcome": "closed", "assumptions": [],
                    "closure_scope": "compiler candidate; MCP checkpoint still required"}
    try:
        goals = decode_goals(output)
    except ValueError as error:
        return {**result, "outcome": "capture-error", "capture_error": str(error)}
    proof_name = re.escape(lemma) if lemma else r"[^)]+"
    incomplete = re.search(r"Error:\s*\(in proof " + proof_name + r"\):\s*"
                           r"Attempt to save an incomplete proof", output)
    returned = "RULE-COMPARE-RETURNED" in output
    if exit_code and goals and incomplete and returned:
        first = {**goals[0], "class": residual_class(goals[0])}
        return {"outcome": "residual:" + first["class"],
                "first_residual": first, "goals": goals}
    if exit_code and incomplete and "[Show~Existentials.]" in output and not goals:
        # Legacy records can establish a returned shelf-only proof, but cannot
        # establish its complete targets. Keep this explicit instead of guessing.
        first = {"class": "shelved-unavailable", "conclusion": None,
                 "context": None, "reason": "The shelf targets were not captured."}
        return {"outcome": "residual:shelved-unavailable",
                "first_residual": first, "goals": [], "shelf": "unavailable"}
    if not returned:
        return {**result, "outcome": "tactic-error"}
    return {**result, "outcome": "compiler-error", "goals": goals}


def trace_rule_name(switch):
    """Use the backend registry. A switch without an observer cannot run."""
    from trace_block_mcp import rule_name_for_switch
    return rule_name_for_switch(switch.rsplit(".", 1)[-1])


def capture_arm_trace(row, *, arm, workspace, root, block, switch, prepared,
                      out, runner=None, keyed_lemma=None):
    """Link a complete live traversal to the exact measured arm.

    A failing arm requests its first residual. Every traversal observes all
    selected rule entries. Closed arms request the selected rule's entries.
    Incomplete traces leave compiler outcomes intact and block publication.
    """
    import trace_block
    source = Path(row["source"])
    rule_set = [{"name": trace_rule_name(switch), "enabled": arm == "rule_on"}]
    rule = rule_set[0]["name"]
    stop = "rule:" + rule if row["outcome"] == "closed" else "residual"
    directory = source.parent / "trace"
    scope = {"root": root, "source": source.relative_to(workspace).as_posix(),
             "source_sha256": digest(source), "statement_sha256": prepared["statement_sha256"],
             "theorem": prepared["lemma"], "switch_class": switch,
             "rule_set": rule_set, "instance_changes": prepared["arm_instances"][arm],
             "keyed_lemma": keyed_lemma,
             "trace_sequence": "Automatic zesu_block stage through first residual or closure. The keyed continuation has separate compiler evidence."}
    record = {"complete": False, "source_scope": scope, "requested_stop": stop,
              "links": {"residual": None, "selected_triggers": {rule: []}}, "errors": []}
    arguments = ["--block", "0x" + block.removeprefix("0x"),
                 "--rules", rule + ("=on" if arm == "rule_on" else "=off"),
                 "--stop", stop, "--workspace", str(workspace),
                 "--source", str(source), "--theorem", prepared["lemma"], "--out", str(directory)]
    record["arguments"] = arguments
    try:
        status = (runner or trace_block.main)(arguments)
        record["exit_code"] = status
        trace_path, markdown = directory / "TRACE.json", directory / "TRACE.md"
        for key, path in (("json", trace_path), ("markdown", markdown)):
            if not path.is_file():
                record["errors"].append("The generator did not produce " + path.name + ".")
            else:
                record[key] = {"path": path.relative_to(out).as_posix(), "sha256": digest(path)}
        if "json" not in record or "markdown" not in record:
            return record
        trace = json.loads(trace_path.read_text())
        # Recheck the stable record rather than trusting its completeness flag.
        validated = trace_block.build_trace(trace.get("request", {}), trace)
        if markdown.read_text() != trace_block.render_markdown(trace):
            record["errors"].append("The Markdown does not render the linked trace record.")
        if status != 0 or not validated["completion"]["trace_complete"]:
            record["errors"].append("The generator returned incomplete trace coverage.")
            record["errors"].extend(validated["completion"]["reasons"])
        identity, request = trace.get("identity", {}), trace.get("request", {})
        for field in ("root", "source_sha256", "statement_sha256"):
            if identity.get(field) != scope[field]:
                record["errors"].append("The trace has a different " + field + ".")
        if request.get("rule_set") != rule_set:
            record["errors"].append("The trace has a different switch assignment.")
        trace_scope = request.get("scope", {})
        if trace_scope.get("source_sha256") != scope["source_sha256"]:
            record["errors"].append("The trace request does not bind the measured arm source.")
        switches = identity.get("switches", {})
        if not isinstance(switches.get("actual_instances"), list):
            record["errors"].append("The trace lacks measured switch instances.")
        expected_stop = trace_block.parse_stop(stop)
        if request.get("stop") != expected_stop:
            record["errors"].append("The trace has a different requested checkpoint.")
        counts = trace.get("coverage", {}).get("entry_events", {})
        if rule not in counts:
            record["errors"].append("The selected rule lacks an entry-coverage record.")
        for index, point in enumerate(trace.get("points", [])):
            trigger = point.get("trigger", {})
            if trigger.get("kind") == "rule-entry" and trigger.get("rule") == rule:
                record["links"]["selected_triggers"][rule].append(
                    record["json"]["path"] + "#" + trace_block.pointer("points", index))
        if trace.get("residual") is not None:
            record["links"]["residual"] = record["json"]["path"] + "#/residual"
        if row["outcome"] != "closed" and record["links"]["residual"] is None:
            record["errors"].append("The failing arm lacks a residual trace link.")
        automatic_closed = validated["completion"].get("proof_closed") is True
        record["stages"] = {"automatic": {"command": "zesu_block.",
            "proof_closed": automatic_closed, "residual": record["links"]["residual"],
            "trace": record["json"]["path"]}}
        if keyed_lemma:
            stages = row.get("compiler_stages", {})
            record["stages"]["keyed_continuation"] = {
                "command": "apply " + keyed_lemma + ".", "evidence_scope": "compiler sequence after zesu_block",
                "started": stages.get("keyed_started", False), "returned": stages.get("keyed_returned", False),
                "sequence_proof_closed": row["outcome"] == "closed",
                "compiler_log": row.get("log"), "compiler_log_sha256": row.get("log_sha256")}
            if row["outcome"] == "closed" and not all(stages.get(key) is True for key in
                    ("automatic_returned", "keyed_started", "keyed_returned")):
                record["errors"].append("The compiler closure lacks explicit keyed-stage evidence.")
        elif row["outcome"] == "closed" and not automatic_closed:
            record["errors"].append("The automatic trace did not reproduce the compiler closure.")
        if digest(source) != scope["source_sha256"]:
            record["errors"].append("The measured source changed during trace capture.")
        record["complete"] = not record["errors"]
    except (Exception, SystemExit) as error:
        # An operational capture failure must not erase the measured arm row.
        record["errors"].append(type(error).__name__ + ": " + str(error))
    return record


def compiler_stages(output):
    return {name: re.search(r"(?m)^" + marker + r"\s*$", output) is not None
            for name, marker in (("automatic_returned", "RULE-COMPARE-AUTOMATIC-RETURNED"),
                                 ("keyed_started", "RULE-COMPARE-KEYED-BEGIN"),
                                 ("keyed_returned", "RULE-COMPARE-KEYED-RETURNED"))}


def comparison_complete(arms, *, no_trace=False):
    """Require compiler results and any requested trace coverage."""
    return set(arms) == {"rule_off", "rule_on"} and all((row["outcome"] == "closed" or row["outcome"].startswith("residual:"))
               and (no_trace or row.get("trace", {}).get("complete") is True) for row in arms.values())


def compare(module, switch, build, out, schema, lemma=None, keyed_lemma=None, *, trace_runner=None, no_trace=True):
    workspace = Path(__file__).resolve().parents[2]
    module, build, out = module.resolve(), build.resolve(), out.resolve()
    if not module.is_relative_to(workspace) or not build.is_relative_to(workspace):
        raise ValueError("The source and private build must belong to this workspace.")
    if not out.is_relative_to(workspace / "_build"):
        raise ValueError("Comparison evidence must use a private _build directory.")
    if not no_trace:
        trace_rule_name(switch)  # Reject unsupported observers before native compilation.
    schema_value = json.loads(schema.read_text())
    required = {"slot", "hand_lines", "rule_on", "rule_off", "seconds", "peak_gib", "mcp_record"}
    if not required <= schema_value["block_record_schema"].keys():
        raise ValueError("The coordinator metrics schema is incompatible.")
    out.mkdir(parents=True, exist_ok=False)
    schema_snapshot = out / "metrics-schema.json"
    schema_snapshot.write_bytes(schema.read_bytes())
    original_hash = digest(module)
    root = subprocess.check_output(["git", "-C", str(workspace), "rev-parse", "HEAD"], text=True).strip()
    prepared = prepare(module, workspace, switch, lemma, keyed_lemma)
    recipe = out / "compiler-recipe.json"
    recipe_hash = snapshot_recipe(build, recipe)
    findlib_path = build / "coqc-ocamlpath.json"
    findlib = json.loads(findlib_path.read_text())
    if findlib["workspace"] != str(workspace) or findlib["private_build"] != str(build):
        raise ValueError("The compiler findlib record belongs to another workspace.")
    env = {"ZESU_SCRATCH_RECIPE": str(recipe), "ZESU_SCRATCH_RECIPE_SHA256": recipe_hash}
    env["OCAMLPATH"] = findlib["OCAMLPATH"]
    # The recorder measures the actual coqc child inside the guarded 64 GiB scope.
    os.environ.update(env)
    policy = coqc_primary.budget_policy(memory_gib=64, diagnostic_probe=True)
    arms = {}
    block = prepared["lemma"].removeprefix("DesignedBoundary_")
    for arm in ("rule_off", "rule_on"):
        directory = out / arm
        directory.mkdir()
        source = directory / module.name
        source.write_text(prepared["copies"][arm])
        done, output, log, compiler, wall = coqc_primary.compile_source(
            source, directory, build, policy=policy)
        result = classify(done.returncode, output, compiler, prepared["lemma"])
        result["compiler_stages"] = compiler_stages(output)
        result.update(source=str(source), source_sha256=digest(source),
                      instance_changes=prepared["arm_instances"][arm],
                      log=str(log), log_sha256=digest(log),
                      exit_code=done.returncode, compiler=compiler,
                      total_wall_seconds=wall,
                      seconds=compiler["cpu_seconds"] if compiler else None,
                      peak_gib=compiler["peak_rss_kib"] / 1024**2 if compiler else None,
                      measurement_scope="actual coqc process; scope limits recorded separately",
                      group_coverage={"active": "recorded before Unshelve",
                                      "shelf": "post-unshelve targets include surviving active goals",
                                      "stack": "unavailable", "given_up": "unavailable"})
        if no_trace:
            result["trace"] = {"complete": False, "skipped": True,
                               "reason": "Tracing is disabled."}
        else:
            try:
                result["trace"] = capture_arm_trace(
                    result, arm=arm, workspace=workspace, root=root, block=block,
                    switch=switch, prepared=prepared, out=out, runner=trace_runner, keyed_lemma=keyed_lemma)
            except ValueError as error:
                result["trace"] = {"complete": False, "errors": [str(error)]}
        save(directory / "evidence.json", result)
        arms[arm] = result
        assert digest(module) == original_hash
    successful = comparison_complete(arms, no_trace=no_trace)
    report = {"root": root, "trace_coverage_complete": all(row["trace"]["complete"] for row in arms.values()),
              "trace_link_base": "Paths resolve relative to this report directory.",
              "block": block, "source": str(module), "source_sha256": original_hash,
              "switch": switch, "imports": prepared["imports"],
              "statement": prepared["statement"], "statement_sha256": prepared["statement_sha256"],
              "existing_instances": prepared["existing_instances"],
              "arm_instances": prepared["arm_instances"], "keyed_lemma": keyed_lemma,
              "comparison_convention": "OFF removes the imported switch instances; ON retains them or adds a local instance when none exists.",
              "proof_budget": policy, "schema_sha256": digest(schema_snapshot), "arms": arms,
              "compiler_recipe": {"path": str(recipe), "sha256": recipe_hash},
              "findlib_record": {"path": str(findlib_path), "sha256": digest(findlib_path)},
              "comparison_success": successful}
    save(out / "report.json", report)
    if successful:
        metrics = {"block": block, "slot": "auto" if module.parent.name == "Auto" else "hand",
                   "hand_lines": prepared["original_hand_lines"],
                   "rule_on": arms["rule_on"]["outcome"], "rule_off": arms["rule_off"]["outcome"],
                   "seconds": arms["rule_on"]["seconds"], "peak_gib": arms["rule_on"]["peak_gib"],
                   "measurement_arm": "rule_on", "mcp_record": None,
                   "traces": {arm: row["trace"] for arm, row in arms.items()},
                   "first_residual": {arm: row["first_residual"] for arm, row in arms.items()},
                   "per_arm": {arm: {key: row[key] for key in ["seconds", "peak_gib", "total_wall_seconds"]}
                               for arm, row in arms.items()},
                   "evidence": {"path": str(out / "report.json"), "sha256": digest(out / "report.json")}}
        save(out / "metrics.json", metrics)
    return report


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("module", type=Path)
    parser.add_argument("switch")
    parser.add_argument("--build-dir", type=Path, required=True)
    parser.add_argument("--out", type=Path, required=True)
    parser.add_argument("--schema", type=Path, required=True)
    parser.add_argument("--lemma")
    parser.add_argument("--keyed-lemma")
    parser.add_argument("--no-trace", action="store_true", default=True,
                        help="Compare compiler results without trace tools (the default).")
    args = parser.parse_args()
    report = compare(args.module, args.switch, args.build_dir, args.out, args.schema,
                     args.lemma, args.keyed_lemma, no_trace=args.no_trace)
    print(json.dumps({"report": str(args.out / "report.json"),
                      "comparison_success": report["comparison_success"],
                      "outcomes": {arm: row["outcome"] for arm, row in report["arms"].items()}}))
    return 0 if report["comparison_success"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
