#!/usr/bin/env python3
"""Re-run the automation, with no step cap, where the replay's cap hit.

The replay runs `once (timeout 30 zesu_block)` at every proof state, and
the message probe says which of those calls ended on the timeout. The 30
seconds is the probe's guard, not a property of the proof, so this tool
goes back to each such state and runs `zesu_block` with no step cap: the
only limits are the 6 GiB fence and a wall limit for the whole file.

Each state is one file: the lemma's own proof up to the step, then

    all: time "UNCAPPED" (first [once zesu_block; idtac "RAN" | idtac "RAISED"]).

and the goals left after it. The result says how long the automation
really takes there and what it ends at: `closed` (no goal left),
`residual` (a goal left, with its class), `raised`, or `timeout` (the
wall limit).
"""

from __future__ import annotations

import argparse
import json
import os
import re
import subprocess
import sys
import time
from concurrent.futures import ThreadPoolExecutor, as_completed
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

from modules import find_proof  # noqa: E402
from sentences import opener_and_steps  # noqa: E402

PROOF_DIR = Path("ZesuSsz/Proofs/WriteSuccess")
GUARD = Path(__file__).resolve().parents[1] / "resource_guard.sh"
TIMED = re.compile(r"Tactic call UNCAPPED ran for (?P<s>[0-9.]+) secs")
END = "UNCAPPED-END"


def states(messages: Path) -> list[tuple[str, str, int]]:
    """Every (module, lemma, step) where the message probe saw the cap."""
    found = []
    for line in messages.read_text().split("\n"):
        if not line:
            continue
        record = json.loads(line)
        for index, text in (record.get("messages") or {}).items():
            if text and "tclTIMEOUT" in text:
                found.append((record["module"], record["lemma"], int(index)))
    return sorted(set(found))


def source(module: Path, lemma: str, step: int,
           imports: list[str]) -> str:
    proof = find_proof(module, lemma)
    opener, steps = opener_and_steps("\n".join(proof.body))
    lines = module.read_text().split("\n")
    body = (["Set Printing Width 200."]
            + [f"Require Import {name}." for name in imports]
            + lines[:proof.proof_line] + ["Proof."] + opener + steps[:step]
            + ['all: time "UNCAPPED" (first [once zesu_block; idtac "RAN" '
               '| idtac "RAISED"]).',
               'all: idtac "LEFT-GOAL".',
               "all: try liShow.", "Show.", "Abort."]
            + [f"End {name}." for name in reversed(proof.open_blocks)]
            + ['Goal True. idtac "UNCAPPED-END". Abort.'])
    return "\n".join(body) + "\n"


def run(item, build_dir: Path, scratch: Path, probe_dir: Path,
        seconds: int, imports: list[str], classify_goal) -> dict:
    module, lemma, step = item
    probe = probe_dir / f"{Path(module).stem}__{lemma}__{step}__uncapped.v"
    probe.write_text(source(PROOF_DIR / module, lemma, step, imports))
    if GUARD.exists():
        subprocess.run([str(GUARD), "wait"], check=False)
    started = time.monotonic()
    done = subprocess.run(
        ["timeout", str(seconds + 60), "nice", "-n", "10", "bash",
         str(scratch), str(probe), str(build_dir)],
        capture_output=True, text=True,
        env={**os.environ, "ZESU_COQC_SECONDS": str(seconds)})
    wall = time.monotonic() - started
    output = done.stdout + "\n" + done.stderr
    calls = [float(found["s"]) for found in TIMED.finditer(output)]
    left = output.count("LEFT-GOAL")
    record = {"module": module, "lemma": lemma, "step": step,
              "wall": round(wall, 1), "automation_seconds": round(sum(calls), 1),
              "goals_run": len(calls), "raised": output.count("\nRAISED")
              + output.startswith("RAISED")}
    if "proof limit exceeded: time" in output or done.returncode == 124:
        record["outcome"] = "timeout"
    elif "proof limit exceeded: memory" in output:
        record["outcome"] = "memory"
    elif END not in output:
        record["outcome"] = "error"
        record["error"] = [line for line in output.split("\n")
                           if line.startswith("Error")][:3]
    elif record["raised"]:
        record["outcome"] = "raised"
    elif left == 0:
        record["outcome"] = "closed"
    else:
        record["outcome"] = "residual"
        shown = output[output.rfind("LEFT-GOAL") + len("LEFT-GOAL"):]
        record["class"] = classify_goal(shown).pred_class if shown.strip() else ""
    return record


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--messages", type=Path, required=True)
    parser.add_argument("--build-dir", type=Path, required=True)
    parser.add_argument("--scratch", type=Path,
                        default=Path("tools/coqc_scratch.sh"))
    parser.add_argument("--classifier", type=Path, required=True)
    parser.add_argument("--import", dest="imports", action="append",
                        default=[])
    parser.add_argument("--seconds", type=int, default=900)
    parser.add_argument("--jobs", type=int, default=16)
    parser.add_argument("--limit", type=int, default=None)
    parser.add_argument("--out", type=Path, required=True)
    arguments = parser.parse_args()

    sys.path.insert(0, str(arguments.classifier))
    from classify import classify_goal  # noqa: E402

    todo = states(arguments.messages)
    done = set()
    if arguments.out.exists():
        for line in arguments.out.read_text().split("\n"):
            if line:
                row = json.loads(line)
                done.add((row["module"], row["lemma"], row["step"]))
    todo = [item for item in todo if item not in done][:arguments.limit]
    print(f"uncapped: {len(todo)} states", file=sys.stderr, flush=True)
    probe_dir = arguments.build_dir / "residuals" / "uncapped"
    probe_dir.mkdir(parents=True, exist_ok=True)
    finished = 0
    with ThreadPoolExecutor(max_workers=arguments.jobs) as pool:
        futures = [pool.submit(run, item, arguments.build_dir,
                               arguments.scratch, probe_dir, arguments.seconds,
                               arguments.imports, classify_goal)
                   for item in todo]
        for future in as_completed(futures):
            row = future.result()
            with arguments.out.open("a") as handle:
                handle.write(json.dumps(row) + "\n")
            finished += 1
            print(f"{finished}/{len(todo)} {row['outcome']} "
                  f"{row['automation_seconds']} s {row['lemma']}:{row['step']}",
                  file=sys.stderr, flush=True)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
