#!/usr/bin/env python3
"""Row 2: generate a chain of segments, junction by junction.

A chain is a run of straight-line segments between two addresses whose
predicates are frozen: written by hand, merged, and not to be changed.
Everything between them is the automation's business.

The loop is one step per junction:

1. probe the segment from the entry predicate known so far to the next
   junction address;
2. if it reaches, the context there *is* the exit boundary. Write it
   with `gen_boundary.py`, and it becomes the entry predicate of the
   next segment. Nothing about it is hand-written and nothing about it
   is guessed;
3. if it stalls, stop. The stall is a ticket with a class and a
   signature, and the chain resumes when the rule for it exists.

The two ends are the exception: each one costs one equivalence lemma,
between the frozen predicate and the inferred boundary beside it. That
is two hand-written lemmas for a chain of any length, which is the whole
point of chaining.
"""

from __future__ import annotations

import argparse
import json
import subprocess
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent


def probe(spec: dict, out: Path, build_dir: Path, rule: Path | None,
          alternatives: list[str], seconds: int) -> dict:
    spec_file = out.with_suffix(".spec.json")
    spec_file.write_text(json.dumps([spec], indent=2) + "\n")
    command = [sys.executable, str(HERE / "infer_boundary.py"),
               "--specs", str(spec_file), "--out", str(out),
               "--build-dir", str(build_dir), "--seconds", str(seconds)]
    if rule:
        command += ["--rule", str(rule)]
    for alternative in alternatives:
        command += ["--alt", alternative]
    subprocess.run(command, check=False)
    text = out.read_text().strip()
    return json.loads(text.split("\n")[-1]) if text else {"outcome": "error"}


def infer_trace(spec: dict, out: Path, build_dir: Path, rule: Path | None,
                alternatives: list[str], seconds: int, rounds: int) -> dict:
    """Grow the segment's declared trace until the block stops asking.

    A boundary has two halves. The resource half is read from the
    context at the exit; the trace half cannot be, because the block
    never gets to the exit while the trace it is handed does not match
    what it emits. So the trace is inferred first, one event a round.
    """
    spec_file = out.with_suffix(".trace.spec.json")
    spec_file.write_text(json.dumps([spec], indent=2) + "\n")
    command = [sys.executable, str(HERE / "infer_trace.py"),
               "--specs", str(spec_file), "--out", str(out),
               "--build-dir", str(build_dir), "--seconds", str(seconds),
               "--rounds", str(rounds)]
    if rule:
        command += ["--rule", str(rule)]
    for alternative in alternatives:
        command += ["--alt", alternative]
    subprocess.run(command, check=False)
    text = out.read_text().strip() if out.exists() else ""
    return json.loads(text.split("\n")[-1]) if text else {}


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--chain", type=Path, required=True)
    parser.add_argument("--out-dir", type=Path,
                        default=Path("ZesuSsz/Evidence/det/chain"))
    parser.add_argument("--build-dir", type=Path,
                        default=Path("_build/agents/det"))
    parser.add_argument("--rule", type=Path, default=None)
    parser.add_argument("--alt", action="append", default=[])
    parser.add_argument("--seconds", type=int, default=1800)
    parser.add_argument("--trace-rounds", type=int, default=12,
                        help="0 skips trace inference and uses the spec "
                             "as written")
    arguments = parser.parse_args()

    chain = json.loads(arguments.chain.read_text())
    arguments.out_dir.mkdir(parents=True, exist_ok=True)
    addresses = ([chain["ends"]["entry"]["address"]]
                 + list(chain["junctions"])
                 + [chain["ends"]["exit"]["address"]])
    entry_spec = chain["ends"]["entry"]["spec"]
    report = []

    for index in range(len(addresses) - 1):
        start, stop = addresses[index], addresses[index + 1]
        name = f"{chain['name']}_{index}"
        spec = {"name": name, "entry": start, "exit": stop,
                "like": chain["like"], "imports": chain["imports"],
                "binders": chain["binders"], "spec": entry_spec}
        # `trace_term` is what the boundary declares today and what the
        # inference replaces; `trace_binder` is the free tail the grown
        # trace ends in. For an internal junction they are the same
        # variable; at a chain end the term is the frozen definition.
        trace_term = (chain.get("trace_term") if index == 0
                      else chain.get("trace_binder"))
        if arguments.trace_rounds and trace_term:
            grown = infer_trace(
                dict(spec, infer_trace=trace_term),
                arguments.out_dir / f"{name}.trace.jsonl",
                arguments.build_dir, arguments.rule, arguments.alt,
                arguments.seconds, arguments.trace_rounds)
            if grown.get("inferred_trace"):
                spec = dict(spec, spec=spec["spec"].replace(
                    trace_term, grown["inferred_trace"]))
                print(f"{name}: {grown['rounds']} trace events inferred",
                      flush=True)
        record = probe(spec, arguments.out_dir / f"{name}.jsonl",
                       arguments.build_dir, arguments.rule, arguments.alt,
                       arguments.seconds)
        report.append({"segment": name, "entry": start, "exit": stop,
                       "outcome": record.get("outcome"),
                       "frame": record.get("frame"),
                       "pred_class": record.get("pred_class"),
                       "signature": record.get("signature")})
        print(f"{name}: {start} -> {stop}: {record.get('outcome')} "
              f"{record.get('pred_class', '')} "
              f"{record.get('signature', '')}", flush=True)
        if record.get("outcome") != "reached":
            print("the chain stops here; the stall above is the ticket",
                  flush=True)
            break
        boundary = arguments.out_dir / f"{name}_boundary.v"
        subprocess.run(
            [sys.executable, str(HERE / "gen_boundary.py"),
             "--records", str(arguments.out_dir / f"{name}.jsonl"),
             "--binders", chain["binders"],
             "--name", f"{chain['name']}Boundary{index + 1}",
             "--out", str(boundary)], check=False)
        exit_spec = (f"{chain['name']}Boundary{index + 1} "
                     + chain.get("boundary_arguments", ""))
        # The segment's own module: two boundaries and `zesu_block`.
        module_spec = dict(spec, exit_spec=exit_spec)
        module_file = arguments.out_dir / f"{name}.module.json"
        module_file.write_text(json.dumps([module_spec], indent=2) + "\n")
        subprocess.run(
            [sys.executable, str(HERE / "gen_segment.py"),
             "--specs", str(module_file), "--out-dir", str(arguments.out_dir),
             "--build-dir", str(arguments.build_dir)], check=False)
        # The inferred boundary is the next segment's entry predicate.
        entry_spec = exit_spec

    (arguments.out_dir / "chain.jsonl").write_text(
        "".join(json.dumps(row) + "\n" for row in report))
    reached = sum(1 for row in report if row["outcome"] == "reached")
    print(f"{reached} of {len(addresses) - 1} junctions reached")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
