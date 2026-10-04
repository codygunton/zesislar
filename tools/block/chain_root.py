#!/usr/bin/env python3
"""Capture native states forward from the Level 1 entry.

Captures are diagnostics, not contract proofs. Pending arithmetic remains
attached to each state. A join retains every incoming state. The driver
checks subsumption at each back edge and stops that path without unrolling.
"""
from __future__ import annotations

import argparse
from copy import deepcopy
from concurrent.futures import FIRST_COMPLETED, ThreadPoolExecutor, wait
import hashlib
import json
import os
import re
from pathlib import Path
import sys
import time
import subprocess

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
sys.path.insert(0, str(HERE.parent / "det"))
sys.path.insert(0, str(HERE.parent / "residual"))
import gen_block
import infer_boundary
import probes
from chain_state import normalize_successor, render_successor
from chain_subsumption import check_subsumption
from chain_goals import RECORDER, recording, parse_goals


def atomic_json(path: Path, value) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_name(path.name + ".tmp")
    temporary.write_text(json.dumps(value, indent=2) + "\n")
    temporary.replace(path)


def fingerprint(state: dict) -> str:
    payload = {key: state.get(key) for key in
               ("binders", "coq", "persistent", "spatial", "local_sorts", "pending_goals",
                "memory_word_widths", "trace_value_widths", "address_widths")}
    # Empty shelves retain the existing frozen probe identities.
    if state.get("shelved_goals"):
        payload["shelved_goals"] = state["shelved_goals"]
    return hashlib.sha256(json.dumps(payload, sort_keys=True).encode()).hexdigest()[:16]



def inherited_debts(state):
    """Keep predecessor debts in every outcome, including parser failures."""
    return {kind: deepcopy(state.get(kind, []))
            for kind in ("pending_goals", "shelved_goals")}


def graph(cfg: dict, root: int) -> dict[int, dict]:
    functions = [row for row in cfg["functions"]
                 if gen_block.address(row.get("entry", row.get("start"))) == root]
    if len(functions) != 1:
        raise ValueError("The CFG must identify exactly one root function.")
    function = functions[0]
    blocks = {}
    for original in function["blocks"]:
        block = dict(original)
        if "instructions" not in block and "rows" in function:
            block["instructions"] = [row for row in function["rows"]
                                     if gen_block.address(block["start"]) <= gen_block.address(row["pc"]) < gen_block.address(block["end"])]
        blocks[gen_block.address(block["start"])] = block
    return blocks


def terminal_target(value):
    """Return a numeric PC or an explicit symbolic Rocq address expression."""
    if isinstance(value, int):
        return value
    text = value.strip()
    if re.fullmatch(r"(?:0x[0-9a-fA-F]+|[0-9]+)", text):
        return int(text, 0) if text.startswith("0x") else int(text)
    if not text or not re.fullmatch(r"[A-Za-z0-9_'(). +*%/-]+", text):
        raise ValueError("The symbolic terminal has invalid characters.")
    if re.search(r"\.(?:\s|$)", text) or text.count("(") != text.count(")"):
        raise ValueError("The symbolic terminal is not one address expression.")
    return text


def boundary_label(target):
    """Name a diagnostic boundary without requiring a concrete address."""
    return f"{target:x}" if isinstance(target, int) else "return_" + hashlib.sha256(target.encode()).hexdigest()[:16]


def boundary_address(target):
    return hex(target) if isinstance(target, int) else target


def boundary_stop(target):
    return infer_boundary.stop_name(hex(target)) if isinstance(target, int) else "CHAIN_STOP_" + boundary_label(target)


def boundary_statement(source, target):
    """Add a continuation without deleting the current instr_body conclusion."""
    lines = source.splitlines()
    name = boundary_stop(target)
    for index, line in enumerate(lines):
        if line.startswith("Lemma infer_boundary ") and line.rstrip().endswith(":"):
            lines[index] = line.rstrip()[:-1] + f" ({name} : iProp Sigma) :"
            position = next((row for row in range(index + 1, len(lines))
                             if "instr_lookup_resources" in lines[row]), index + 1)
            address = hex(target) if isinstance(target, int) else f"({target})"
            lines.insert(position, f"  instr_pre {address} {name} -∗")
            return "\n".join(lines)
    raise ValueError("The probe has no lemma binder boundary.")


def probe_source(spec, options, successor):
    source = infer_boundary.spec_source(spec, stop=None, after_return=True)
    source = boundary_statement(source, successor)
    if isinstance(successor, int):
        # Retain the numeric recorder layout for frozen capture identities.
        source = source.replace("all: try zesu_enter_return_wand_if_enabled.\nall: try liShow.",
                                "all: try zesu_enter_return_wand_if_enabled.\n\nall: try liShow.")
    if options:
        source = source.replace("\n".join(infer_boundary.CODE_PREMISES),
                                "\n".join(options["code_premises"]))
        source = re.sub(r"^From \S+ Require Import Index\.$",
                        "Require Import " + options["trace_import"] + ".", source, flags=re.M)
    return source


def compile_probe(source, name, build, seconds, options):
    if not options:
        return infer_boundary.run(source, name, build, seconds)
    directory = Path(options["stage_dir"])
    directory.mkdir(parents=True, exist_ok=True)
    path = directory / f"{name}.v"
    path.write_text(source)
    environment = {**os.environ, "ZESU_COQC_SECONDS": str(seconds)}
    done = subprocess.run(
        ["timeout", str(seconds + 60), "nice", "-n", "10", "bash",
         str(infer_boundary.SCRATCH), str(path), str(build)],
        capture_output=True, text=True, env=environment)
    return done.stdout + "\n" + done.stderr


def back_edges(blocks: dict[int, dict], root: int) -> set[tuple[int, int]]:
    """Use DFS ancestry, rather than numeric address order."""
    active, done, result = set(), set(), set()

    def visit(pc):
        if pc not in blocks or pc in done:
            return
        active.add(pc)
        for value in blocks[pc]["successors"]:
            successor = gen_block.address(value)
            if successor in active:
                result.add((pc, successor))
            else:
                visit(successor)
        active.remove(pc)
        done.add(pc)

    visit(root)
    return result


def load_invariant_hints(path, blocks, root):
    """Validate design metadata against the CFG without assuming its obligations."""
    if path is None:
        return {}
    design = json.loads(path.read_text())
    if gen_block.address(design["entry_pc"]) != root:
        raise ValueError("The invariant design has a different root.")
    headers = {target for _, target in back_edges(blocks, root)}
    result = {}
    for row in design["blocks"]:
        hint = row.get("invariant_hint")
        if not hint:
            continue
        pc = gen_block.address(hint["header_pc"])
        if pc != gen_block.address(row["entry_pc"]) or pc not in headers:
            raise ValueError("The invariant hint does not identify a CFG header.")
        if pc in result:
            raise ValueError("The invariant design repeats a header.")
        successors = {gen_block.address(value) for value in blocks[pc]["successors"]}
        if gen_block.address(hint["exit"]) not in successors:
            raise ValueError("The invariant exit is not a header successor.")
        preheader = gen_block.address(hint["preheader"])
        if preheader not in blocks or pc not in {
                gen_block.address(value) for value in blocks[preheader]["successors"]}:
            raise ValueError("The invariant preheader does not enter its header.")
        for group in ("pure_lemmas", "machine_obligations"):
            for kind in ("entry", "preservation", "exit"):
                if not re.fullmatch(r"[A-Za-z_][A-Za-z0-9_.]*", hint[group][kind]):
                    raise ValueError("The invariant reference has an invalid Rocq name.")
        bindings = hint["register_bindings"]
        for parameter in hint["symbolic_parameters"].values():
            if "register" in parameter and bindings.get(parameter["register"]) != parameter["register_value"]:
                raise ValueError("A symbolic parameter conflicts with its register binding.")
            for register, value in parameter.get("register_bindings", {}).items():
                if bindings.get(register) != value:
                    raise ValueError("A symbolic pointer conflicts with its register binding.")
        result[pc] = {**hint, "design_sha256": hashlib.sha256(path.read_bytes()).hexdigest()}
    if headers != set(result):
        raise ValueError("The invariant design does not cover every CFG header.")
    return result


def invariant_obligations(hints):
    """Keep machine obligations separate from captures and pure helper lemmas."""
    return [{"header": hex(pc), "kind": kind, "status": "pending",
             "machine_obligation": hint["machine_obligations"][kind],
             "pure_helper": hint["pure_lemmas"][kind],
             "design_sha256": hint["design_sha256"], "capture_only": True,
             "reason": "The machine obligation is an unproved proposition."}
            for pc, hint in sorted(hints.items())
            for kind in ("entry", "preservation", "exit")]



def generalized_header(state, hint):
    """Use the approved named predicate; retain binders, provenance, and debts."""
    predicate = hint["rocq_predicate"]
    if not re.fullmatch(r"[A-Za-z_][A-Za-z0-9_.]*", predicate):
        raise ValueError("The header predicate has an invalid Rocq name.")
    kinds = gen_block.gen_boundary.binder_types(state["binders"])
    if kinds.get("args") != "DecodeItemArgs":
        raise ValueError("The header template requires the existing DecodeItemArgs binder args.")
    header = deepcopy(state)
    pc = gen_block.address(hint["header_pc"])
    header.update(name=f"GeneralizedHeader_{pc:x}", entry=pc, state_entry=pc,
                  coq=[], persistent=[], local_sorts={},
                  spatial=["∃ (n i payloadStart : Z) (lengthBytes frameBytes : list byte) "
                           f"(loaded : bv 64), {predicate} {hex(pc)} args "
                           "n i payloadStart lengthBytes frameBytes loaded"],
                  imports=list(dict.fromkeys([*state.get("imports", []), predicate.rsplit(".", 1)[0]])),
                  generalization={"header": hex(pc), "predicate": predicate,
                                  "symbolic_parameters": deepcopy(hint["symbolic_parameters"]),
                                  "register_bindings": deepcopy(hint["register_bindings"]),
                                  "design_sha256": hint["design_sha256"]})
    # Captured widths describe concrete resources, not the folded predicate.
    for key in ("context", "memory_word_widths", "trace_value_widths", "address_widths"):
        header.pop(key, None)
    return header


def establish_header(state, hint, build, seconds):
    """Accept a generalization only after a compiled, debt-free entailment."""
    header = generalized_header(state, hint)
    result = check_subsumption(state, header, build, seconds)
    return header, result

def residual_pc_markers(output):
    markers = re.findall(r"CHAIN-RESIDUAL-PC([^\n]*)", output)
    result = []
    for marker in markers:
        match = re.fullmatch(
            r"\s*\(?(?:bv_to_bvn\s*\()?Z_to_bv\s+64\s+(0x[0-9a-fA-F]+|\d+)\s*\)*\s*",
            marker)
        if match:
            result.append(int(match.group(1), 0))
    return result, "known" if markers and len(markers) == len(result) else "unknown"


def render_probe(state: dict, block: dict, successor: int | str) -> str:
    leader = gen_block.address(block["start"])
    token = fingerprint(state)
    name = f"chain_{leader:x}_{boundary_label(successor)}_{token}"
    arguments = state.get("arguments", gen_block.gen_boundary.explicit_arguments(state["binders"]))
    _, callee_modules, _ = gen_block.call_sites.premises(
        leader, gen_block.address(block["end"]), strict=True)
    imports = list(dict.fromkeys([*state.get("imports", []), *callee_modules,
                                  "ZesuSsz.Automation.Sets.call"]))
    spec = {"name": name, "entry": hex(leader), "exit": hex(gen_block.address(block["end"])),
            "binders": state["binders"], "imports": imports,
            "spec": f"{state['name']} {arguments}".strip()}
    source = probe_source(spec, state.get("probe_options", {}), successor)
    # The native recorder identifies the stop conclusion. A separate check
    # cannot refer to that binder in pure goals that discarded it.
    if isinstance(successor, int):
        source = source.replace("\n".join(infer_boundary.stop_recording(hex(successor), False)), "")
    # Inline the generated declaration. The scratch compiler consumes the
    # pinned build recipe without concurrent writes to its library artifacts.
    marker = "Lemma infer_boundary "
    other = [gen_block.address(value) for value in block["successors"]
             if gen_block.address(value) != successor]
    for pc in other:
        source = boundary_statement(source, pc)
    source = source.replace(marker, RECORDER + "\n" + render_successor(state) + "\n" + marker, 1)
    table = gen_block.call_sites.contracts()
    targets = {target for pc, (target, _) in gen_block.call_sites.call_sites().items()
               if leader <= pc < gen_block.address(block["end"])}
    unfolds = list(dict.fromkeys(table[target]["name"] for target in sorted(targets)
                                if table[target].get("local_unfold", False)))
    instances = "\n".join(f"#[local] Instance : LithiumUnfold (@{callee}) := I.\n"
                          f"#[local] Typeclasses Opaque {callee}." for callee in unfolds)
    source = source.replace(marker, instances + "\n" + marker, 1)
    begin = source.index(f'all: idtac "{infer_boundary.RAW_BEGIN}".')
    end = source.index("Abort.", begin) + len("Abort.")
    marker = r'''all: try (lazymatch goal with
  | |- envs_entails ?D _ => lazymatch D with
      | context [reg_mapsto _ "PC" _ (RVal_Bits ?v)] => idtac "CHAIN-RESIDUAL-PC" v
      end
  end).
'''
    source = (source[:begin] + marker + recording("active") + "\nUnshelve.\nall: try liShow.\n"
              + recording("shelved") + "\nAbort." + source[end:])
    return "Require Import ZesuSsz.Automation.All.\n" + source


def parse_probe(output: str, state: dict, block: dict, successor: int | str) -> list[dict]:
    """Parse diagnostic captures without treating them as proved contracts."""
    leader = gen_block.address(block["start"])
    token = fingerprint(state)
    _, callee_modules, _ = gen_block.call_sites.premises(
        leader, gen_block.address(block["end"]), strict=True)
    imports = list(dict.fromkeys([*state.get("imports", []), *callee_modules,
                                  "ZesuSsz.Automation.Sets.call"]))
    other = [gen_block.address(value) for value in block["successors"]
             if gen_block.address(value) != successor]
    goals = parse_goals(output, phase="active")
    shelved = parse_goals(output, phase="shelved")
    def identity(goal):
        return {key: goal.get(key) for key in
                ("coq", "persistent", "spatial", "conclusion", "local_sorts",
                 "memory_word_widths", "trace_value_widths", "address_widths")}
    shelved = [goal for goal in shelved if not any(identity(goal) == identity(active) for active in goals)]
    target = boundary_stop(successor)
    reached = [goal for goal in goals if goal["environment"] == "iris"
               and goal["conclusion"].strip() == target]
    record = {"entry": hex(leader), "exit": boundary_address(successor),
              "state_entry": boundary_address(successor), "binders": state["binders"],
              "imports": imports, "predecessor_fingerprint": token,
              "root_provenance": state.get("root_provenance"),
              "capture_only": True, "elapsed_seconds": 0,
              "inherited_debts": inherited_debts(state),
              "pending_goals": [goal for goal in goals if not any(
                  goal["conclusion"].strip() == infer_boundary.stop_name(hex(pc))
                  for pc in other) and goal["conclusion"].strip() != target]}
    record["shelved_goals"] = shelved
    record["raw_goals"] = output
    record["residual_pcs"], record["residual_location"] = residual_pc_markers(output)
    measurements = re.findall(r"exit=(-?\d+) ms=(\d+) rss_kb=(\d+)", output)
    if measurements:
        rc, milliseconds, rss = map(int, measurements[-1])
        record["performance"] = {"rc": rc, "wall_seconds": milliseconds / 1000,
                                  "peak_mib": rss / 1024}
    if probes.END not in output or not measurements or rc != 0:
        record.update(outcome="error", error_lines=output.splitlines()[-12:])
    elif not goals and not shelved and "No more goals." in output:
        record.update(outcome="closed")
    elif reached:
        return [{**record, **goal, "outcome": "reached"} for goal in reached]
    elif goals and not record["shelved_goals"] and all(
            any(goal["conclusion"].strip() == infer_boundary.stop_name(hex(pc))
                for pc in other) for goal in goals):
        record.update(outcome="unreachable-successor", coq=[], spatial=[])
    elif goals and all(goal["conclusion"].strip() == "False" for goal in goals):
        # A False goal is a failure, not a proof of an unreachable path.
        record.update(outcome="stalled")
    else:
        record.update(outcome="stalled")
    return [record]


def probe(state: dict, block: dict, successor: int | str, build: Path,
          seconds: int) -> list[dict]:
    source = render_probe(state, block, successor)
    leader = gen_block.address(block["start"])
    name = f"chain_{leader:x}_{boundary_label(successor)}_{fingerprint(state)}"
    subprocess.run([str(HERE.parent / "resource_guard.sh"), "wait"], check=True)
    output = compile_probe(source, name, build, seconds, state.get("probe_options", {}))
    return parse_probe(output, state, block, successor)


def write_baseline(path, blocks, captures):
    observations = {}
    for record in captures:
        observations.setdefault(gen_block.address(record["entry"]), []).append(record)
    rows = []
    first_residuals = {}
    for pc in sorted(blocks):
        records = observations.get(pc, [])
        outcomes = []
        for record in records:
            outcome = record["outcome"]
            if outcome == "stalled":
                locations = record.get("residual_pcs", [])
                outcome = ("unknown-stall" if not locations or record.get("residual_location") == "unknown" else
                           "entry-stall" if all(value == pc for value in locations) else
                           "execution-stall")
                residual = (record.get("pending_goals") or record.get("shelved_goals") or [
                    {"raw_goals": record.get("raw_goals", "")}])[0]
                first_residuals.setdefault(outcome, {"entry": hex(pc), "residual": residual,
                                                   "residual_pcs": locations})
            outcomes.append(outcome)
        rows.append({"entry": hex(pc), "outcomes": outcomes or ["missing-entry"],
                     "observations": len(records)})
    atomic_json(path, {"schema": 1, "capture_only": True, "block_count": len(blocks),
                       "blocks": rows, "first_residuals": first_residuals})


def run(args) -> int:
    states = gen_block.read_states(args.entries)
    root = gen_block.address(args.root)
    blocks = graph(json.loads(args.cfg.read_text()), root)
    if root not in states:
        if getattr(args, "baseline_out", None):
            write_baseline(args.baseline_out, blocks, [])
        raise ValueError("the Level 1 root state is missing")
    loops = back_edges(blocks, root)
    root_state = states[root]
    provenance = root_state.get("root_provenance", {})
    declaration = getattr(args, "root_declaration", None)
    if not provenance.get("source") or (declaration and provenance["source"] != declaration):
        raise ValueError("The Level 1 root declaration is not identified.")
    checked_source = getattr(args, "root_source", None)
    if checked_source and render_successor(root_state) != checked_source.read_text():
        raise ValueError("The root resources differ from the checked Level 1 state.")
    terminal = terminal_target(args.terminal)
    hints = load_invariant_hints(getattr(args, "invariant_hints", None), blocks, root)
    obligations = invariant_obligations(hints)
    root_state["name"] = f"NativeRootState_{root:x}"
    if getattr(args, "trace_import", None):
        root_state["probe_options"] = {
            "trace_import": args.trace_import, "stage_dir": str(args.stage_dir),
            "code_premises": args.code_premises.read_text().splitlines()}
        infer_boundary.PROOF_DIR = args.proof_dir
    root_state["root_provenance"] = {**provenance, "entry": hex(root),
        "capture_source": str(args.entries),
        "capture_sha256": hashlib.sha256(args.entries.read_bytes()).hexdigest()}
    root_state["chain_path"] = [hex(root)]
    queue = [(root, root_state)]
    headers = {root: root_state}
    root_generalization = None
    if root in hints:
        header, root_generalization = establish_header(root_state, hints[root],
            args.build_dir, args.seconds)
        if root_generalization.get("outcome") == "closed":
            queue, headers = [(root, header)], {root: header}
        else:
            queue, headers = [], {}
    seen, captures, futures = set(), [], {}
    furthest = (0, root)
    worker_limit = 1
    measured_peak = 0
    args.out.mkdir(parents=True, exist_ok=True)
    if hints:
        atomic_json(args.out / "invariant_obligations.json", obligations)
    with ThreadPoolExecutor(max_workers=args.jobs) as pool:
        while queue or futures:
            while queue and len(futures) < worker_limit:
                leader, state = queue.pop(0)
                key = (leader, fingerprint(state))
                if key in seen or leader not in blocks:
                    continue
                seen.add(key)
                block = blocks[leader]
                if not block["successors"] and isinstance(terminal, str):
                    instructions = block.get("instructions", [])
                    if not instructions or instructions[-1].get("kind") != "return":
                        raise ValueError("A symbolic terminal requires a CFG return instruction.")
                for value in (block["successors"] or [terminal]):
                    successor = terminal_target(value)
                    started = time.monotonic()
                    future = pool.submit(probe, state, block, successor, args.build_dir, args.seconds)
                    futures[future] = (leader, successor, state, started)
            if not futures:
                break
            finished, _ = wait(futures, return_when=FIRST_COMPLETED)
            for future in finished:
                leader, successor, state, started = futures.pop(future)
                try:
                    candidates = future.result()
                    if isinstance(candidates, dict):
                        candidates = [candidates]
                except Exception as error:
                    candidates = [{"entry": hex(leader), "exit": boundary_address(successor),
                                   "outcome": "error", "error": str(error)}]
                for record in candidates:
                    try:
                        record["elapsed_seconds"] = round(time.monotonic() - started, 2)
                        peak = record.get("performance", {}).get("peak_mib")
                        if peak:
                            measured_peak = max(measured_peak, peak)
                            available = next(int(line.split()[1]) / 1024 for line in
                                Path("/proc/meminfo").read_text().splitlines()
                                if line.startswith("MemAvailable:"))
                            worker_limit = min(args.jobs, max(1, int(0.7 * available / measured_peak)))
                        if record["outcome"] in {"reached", "unreachable-successor"}:
                            if successor not in blocks and successor != terminal:
                                raise ValueError(f"unexpected external boundary: {boundary_address(successor)}")
                            next_state = normalize_successor(record, entry=successor,
                                binders=state["binders"], name=f"NativeState_{boundary_label(successor)}_{fingerprint(record)}",
                                imports=state.get("imports", []), provenance=root_state["root_provenance"])
                            next_state["probe_options"] = state.get("probe_options", {})
                            next_state["pending_goals"] = (state.get("pending_goals", [])
                                + state.get("shelved_goals", [])
                                + record["pending_goals"] + record["shelved_goals"])
                            next_state["chain_path"] = state["chain_path"] + [boundary_address(successor)]
                            if record["outcome"] == "reached":
                                furthest = max(furthest, (len(state["chain_path"]), leader))
                            record["derived_state"] = next_state
                            destination = args.out / "States" / f"State_{boundary_label(successor)}.v"
                            destination.parent.mkdir(parents=True, exist_ok=True)
                            path = destination if not destination.exists() else destination.with_name(
                                f"State_{boundary_label(successor)}_{fingerprint(next_state)}.v")
                            path.write_text(render_successor(next_state))
                            if record["outcome"] == "unreachable-successor":
                                record["unreachable"] = True
                            elif successor == terminal:
                                record["terminal"] = True
                            elif successor in hints:
                                hint = hints[successor]
                                record["invariant_hint"] = hint
                                record["back_edge"] = (leader, successor) in loops
                                header = headers.get(successor)
                                if header is None:
                                    header, result = establish_header(next_state, hint,
                                        args.build_dir, args.seconds)
                                else:
                                    result = check_subsumption(next_state, header,
                                        args.build_dir, args.seconds)
                                record["subsumption"] = result
                                record["generalization"] = result
                                record["invariant_edge"] = ("preservation" if record["back_edge"] else "entry")
                                if result.get("outcome") == "closed" and successor not in headers:
                                    headers[successor] = header
                                    queue.append((successor, header))
                                    record["requeued_generalized_header"] = True
                                    (args.out / "States" / f"Header_{successor:x}.v").write_text(
                                        render_successor(header))
                            elif (leader, successor) in loops:
                                record["back_edge"] = True
                                header = headers.get(successor)
                                record["subsumption"] = (check_subsumption(next_state, header,
                                    args.build_dir, args.seconds) if header else
                                    {"outcome": "pending", "reason": "The header state is missing."})
                            else:
                                headers.setdefault(successor, next_state)
                                queue.append((successor, next_state))
                            for header_pc, hint in hints.items():
                                if leader == header_pc and successor == gen_block.address(hint["exit"]):
                                    record["invariant_exit"] = {"header": hex(header_pc),
                                        "machine_obligation": hint["machine_obligations"]["exit"],
                                        "status": "pending", "capture_only": True}
                    except Exception as error:
                        record = {**(record or {}), "entry": hex(leader), "exit": boundary_address(successor),
                                  "outcome": "error", "error": str(error)}
                    record["inherited_debts"] = inherited_debts(state)
                    captures.append(record)
                    if record["outcome"] in {"reached", "unreachable-successor"}:
                        # Preserve the first publisher's canonical capture. Distinct
                        # native incoming states remain available as sidecar files.
                        published = args.publish_dir / f"{leader:x}.json"
                        if published.exists():
                            published = args.publish_dir / f"{leader:x}_{boundary_label(successor)}_{fingerprint(record)}.json"
                        atomic_json(published, record)
                    path = args.out / "post_states" / f"{leader:x}.json"
                    previous = json.loads(path.read_text()) if path.exists() else []
                    if isinstance(previous, dict):
                        previous = [previous]
                    atomic_json(path, previous + [record])
                    atomic_json(args.out / "chain_summary.json", {"root": hex(root),
                        "captures": len(captures), "reached": sum(r["outcome"] == "reached" for r in captures),
                        "furthest_leader": hex(furthest[1]), "chain_depth": furthest[0],
                        "worker_limit": worker_limit,
                        "pending": len(queue) + len(futures)})
                    print(f"{hex(leader)} -> {boundary_address(successor)} {record['outcome']}", flush=True)
    atomic_json(args.out / "chain_summary.json", {"root": hex(root),
        "captures": len(captures), "reached": sum(r["outcome"] == "reached" for r in captures),
        "furthest_leader": hex(furthest[1]), "chain_depth": furthest[0],
        "worker_limit": worker_limit, "pending": 0,
        "errors": sum(r["outcome"] == "error" for r in captures),
        "failed_subsumptions": sum(r.get("subsumption", {}).get("outcome", "closed") != "closed" for r in captures),
        "invariant_obligations": obligations,
        "root_generalization": root_generalization,
        "capture_only": True})
    if getattr(args, "baseline_out", None):
        write_baseline(args.baseline_out, blocks, captures)
    failed = (root_generalization is not None and
              root_generalization.get("outcome") != "closed") or any(
                  record["outcome"] == "error" or
                  record.get("subsumption", {}).get("outcome", "closed") != "closed"
                  for record in captures)
    return 1 if failed or any(row["status"] != "closed" for row in obligations) else 0


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--entries", type=Path, required=True)
    parser.add_argument("--cfg", type=Path, required=True)
    parser.add_argument("--root", required=True)
    parser.add_argument("--terminal", required=True,
                        help="the Level 1 return address: numeric PC or symbolic Rocq expression")
    parser.add_argument("--out", type=Path, required=True)
    parser.add_argument("--publish-dir", type=Path, required=True)
    parser.add_argument("--build-dir", type=Path, required=True)
    parser.add_argument("--jobs", type=int, default=1)
    parser.add_argument("--seconds", type=int, default=300)
    parser.add_argument("--root-declaration", required=True)
    parser.add_argument("--root-source", type=Path, required=True)
    parser.add_argument("--proof-dir", type=Path, required=True)
    parser.add_argument("--stage-dir", type=Path, required=True)
    parser.add_argument("--trace-import", required=True)
    parser.add_argument("--code-premises", type=Path, required=True)
    parser.add_argument("--invariant-hints", type=Path,
                        help="Generalize CFG headers through checked entailments and emit machine obligations.")
    parser.add_argument("--baseline-out", type=Path,
                        help="Write coverage and residuals for the separate block baseline.")
    args = parser.parse_args()
    if not re.fullmatch(r"[A-Za-z_][A-Za-z0-9_.]*", args.trace_import):
        parser.error("The trace import has an invalid name.")
    if not 1 <= args.jobs <= 48:
        parser.error("jobs must be between 1 and 48")
    if not 1 <= args.seconds <= 300:
        parser.error("seconds must be between 1 and 300")
    return run(args)


if __name__ == "__main__":
    raise SystemExit(main())
