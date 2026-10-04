#!/usr/bin/env python3
"""Capture native states forward from the Level 1 entry.

Captures are diagnostics, not contract proofs. Pending arithmetic remains
attached to each state. A join retains every incoming state. The driver
checks subsumption at each back edge and stops that path without unrolling.
"""
from __future__ import annotations

import argparse
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
    return hashlib.sha256(json.dumps(payload, sort_keys=True).encode()).hexdigest()[:16]


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


def probe_source(spec, options, successor):
    source = infer_boundary.spec_source(spec, stop=hex(successor), after_return=True)
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


def probe(state: dict, block: dict, successor: int, build: Path,
          seconds: int) -> list[dict]:
    leader = gen_block.address(block["start"])
    token = fingerprint(state)
    name = f"chain_{leader:x}_{successor:x}_{token}"
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
    source = source.replace("\n".join(infer_boundary.stop_recording(hex(successor), False)), "")
    # Inline the generated declaration. The scratch compiler consumes the
    # pinned build recipe without concurrent writes to its library artifacts.
    marker = "Lemma infer_boundary "
    other = [gen_block.address(value) for value in block["successors"]
             if gen_block.address(value) != successor]
    for pc in other:
        source_lines = source.splitlines()
        source = "\n".join(infer_boundary.stop_statement(source_lines, hex(pc)))
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
    # Admission waiting does not consume the proof's time allowance.
    subprocess.run([str(HERE.parent / "resource_guard.sh"), "wait"], check=True)
    output = compile_probe(source, name, build, seconds, state.get("probe_options", {}))
    goals = parse_goals(output, phase="active")
    shelved = parse_goals(output, phase="shelved")
    def identity(goal):
        return {key: goal.get(key) for key in
                ("coq", "persistent", "spatial", "conclusion", "local_sorts",
                 "memory_word_widths", "trace_value_widths", "address_widths")}
    shelved = [goal for goal in shelved if not any(identity(goal) == identity(active) for active in goals)]
    target = infer_boundary.stop_name(hex(successor))
    reached = [goal for goal in goals if goal["environment"] == "iris"
               and goal["conclusion"].strip() == target]
    record = {"entry": hex(leader), "exit": hex(successor),
              "state_entry": hex(successor), "binders": state["binders"],
              "imports": imports, "predecessor_fingerprint": token,
              "root_provenance": state.get("root_provenance"),
              "capture_only": True, "elapsed_seconds": 0,
              "pending_goals": [goal for goal in goals if not any(
                  goal["conclusion"].strip() == infer_boundary.stop_name(hex(pc))
                  for pc in [successor, *other])]}
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
    seen, captures, futures = set(), [], {}
    furthest = (0, root)
    worker_limit = 1
    measured_peak = 0
    args.out.mkdir(parents=True, exist_ok=True)
    with ThreadPoolExecutor(max_workers=args.jobs) as pool:
        while queue or futures:
            while queue and len(futures) < worker_limit:
                leader, state = queue.pop(0)
                key = (leader, fingerprint(state))
                if key in seen or leader not in blocks:
                    continue
                seen.add(key)
                block = blocks[leader]
                for value in (block["successors"] or [args.terminal]):
                    successor = gen_block.address(value)
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
                    candidates = [{"entry": hex(leader), "exit": hex(successor),
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
                            if successor not in blocks and successor != gen_block.address(args.terminal):
                                raise ValueError(f"unexpected external boundary: {hex(successor)}")
                            next_state = normalize_successor(record, entry=successor,
                                binders=state["binders"], name=f"NativeState_{successor:x}_{fingerprint(record)}",
                                imports=state.get("imports", []), provenance=root_state["root_provenance"])
                            next_state["probe_options"] = state.get("probe_options", {})
                            next_state["pending_goals"] = (state.get("pending_goals", [])
                                + state.get("shelved_goals", [])
                                + record["pending_goals"] + record["shelved_goals"])
                            next_state["chain_path"] = state["chain_path"] + [hex(successor)]
                            if record["outcome"] == "reached":
                                furthest = max(furthest, (len(state["chain_path"]), leader))
                            record["derived_state"] = next_state
                            destination = args.out / "States" / f"State_{successor:x}.v"
                            destination.parent.mkdir(parents=True, exist_ok=True)
                            path = destination if not destination.exists() else destination.with_name(
                                f"State_{successor:x}_{fingerprint(next_state)}.v")
                            path.write_text(render_successor(next_state))
                            if record["outcome"] == "unreachable-successor":
                                record["unreachable"] = True
                            elif successor == gen_block.address(args.terminal):
                                record["terminal"] = True
                            elif (leader, successor) in loops:
                                record["back_edge"] = True
                                header = headers.get(successor)
                                record["subsumption"] = (check_subsumption(next_state, header,
                                    args.build_dir, args.seconds) if header else
                                    {"outcome": "pending", "reason": "The header state is missing."})
                            else:
                                headers.setdefault(successor, next_state)
                                queue.append((successor, next_state))
                    except Exception as error:
                        record = {**(record or {}), "entry": hex(leader), "exit": hex(successor),
                                  "outcome": "error", "error": str(error)}
                    captures.append(record)
                    if record["outcome"] in {"reached", "unreachable-successor"}:
                        # Preserve the first publisher's canonical capture. Distinct
                        # native incoming states remain available as sidecar files.
                        published = args.publish_dir / f"{leader:x}.json"
                        if published.exists():
                            published = args.publish_dir / f"{leader:x}_{successor:x}_{fingerprint(record)}.json"
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
                    print(f"{hex(leader)} -> {hex(successor)} {record['outcome']}", flush=True)
    atomic_json(args.out / "chain_summary.json", {"root": hex(root),
        "captures": len(captures), "reached": sum(r["outcome"] == "reached" for r in captures),
        "furthest_leader": hex(furthest[1]), "chain_depth": furthest[0],
        "worker_limit": worker_limit, "pending": 0,
        "errors": sum(r["outcome"] == "error" for r in captures)})
    if getattr(args, "baseline_out", None):
        write_baseline(args.baseline_out, blocks, captures)
    return 1 if any(record["outcome"] == "error" for record in captures) else 0


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--entries", type=Path, required=True)
    parser.add_argument("--cfg", type=Path, required=True)
    parser.add_argument("--root", required=True)
    parser.add_argument("--terminal", required=True,
                        help="the Level 1 return boundary for CFG ret blocks")
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
