#!/usr/bin/env python3
"""E2: why the expensive probes are expensive.

Iteration 2 counted the top-level conjuncts of the entry predicate's
definition text. A folded predicate counts as one, so that measure said
"median 1" and meant nothing. The frame the proof search actually sees is
the context the probe captured, after the block automation introduced and
atomized the precondition, so this reads the stored goal text instead.

How the three causes are told apart, in order:

- frame size: more than `WIDE_FRAME` hypotheses in the captured context.
- finisher cost: the timed `zesu_run` passes account for less than half of
  the automation time, so the rest went to `zesu_finish` and instance
  resolution, which run outside that timer.
- search blowup: the timed passes account for half or more.

Automation time is the probe's wall time less the module's own compile
cost, which the Dune trace supplies; the probe recompiles the module up to
the target `Proof.` before the automation runs at all.
"""

from __future__ import annotations

import argparse
import collections
import json
import statistics
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

import corpus  # noqa: E402
from costs import module_costs  # noqa: E402
from goals import context_size, conclusion_text  # noqa: E402

GOALS = Path("_build/agents/corpus/residuals")
SLOW_SECONDS = 120.0
WIDE_FRAME = 12
FINISHER_SHARE = 0.5


def stored_context(record: dict, goals: Path) -> str:
    digest = record.get("goal_sha256")
    if not digest:
        return ""
    stored = goals / f"{digest}.txt"
    return conclusion_text(stored.read_text())[0] if stored.exists() else ""


def measure(record: dict, goals: Path, costs: dict) -> dict:
    context = stored_context(record, goals)
    frame, points = context_size(context)
    run_seconds = [float(v) for v in record.get("zesu_run_seconds", [])]
    seconds = float(record.get("seconds", 0.0))
    prefix = costs.get(record["module"], (0.0, 0))[0]
    automation = max(0.0, seconds - prefix)
    inside = sum(run_seconds)
    if not context:
        # A probe that never reached `Show` stored no goal, so its frame is
        # unknown and no cause can be assigned to it honestly.
        cause = "not measured"
    elif frame > WIDE_FRAME:
        cause = "frame size"
    elif automation > 0 and inside < FINISHER_SHARE * automation:
        cause = "finisher cost"
    else:
        cause = "search blowup"
    return {"module": record["module"], "lemma": record["lemma"],
            "outcome": record["outcome"], "seconds": round(seconds, 1),
            "module_seconds": round(prefix, 1),
            "automation_seconds": round(automation, 1),
            "zesu_run_total": round(inside, 2), "passes": len(run_seconds),
            "frame": frame, "mapsto": points,
            "has_context": bool(context), "cause": cause}


def expensive(records: list[dict]) -> list[dict]:
    return [r for r in records
            if r.get("population") == "iris"
            and (r["outcome"] == "timeout"
                 or float(r.get("seconds", 0.0)) >= SLOW_SECONDS)]


def report(rows: list[dict]) -> list[str]:
    lines = [f"expensive probes {len(rows)}: " + " ".join(
        f"{name} {count}" for name, count in
        collections.Counter(r["outcome"] for r in rows).most_common()),
        f"context captured for {sum(1 for r in rows if r['has_context'])}"
        f" of {len(rows)}; a probe that timed out has none",
        "cause, over the probes with a captured context: " + " ".join(
            f"{name} {count}" for name, count in
            collections.Counter(r["cause"] for r in rows
                                if r["has_context"]).most_common()),
        f"cause rule: frame over {WIDE_FRAME} hypotheses; else timed"
        f" zesu_run passes under {FINISHER_SHARE:.0%} of automation time"
        f" is finisher cost, else search blowup"]
    measured = [r for r in rows if r["has_context"]]
    for field in ("frame", "mapsto", "passes", "automation_seconds"):
        values = sorted(r[field] for r in (measured if field in
                                           {"frame", "mapsto"} else rows))
        if not values:
            lines.append(f"{field}: not measured")
            continue
        lines.append(f"{field}: median {statistics.median(values):.1f} "
                     f"p90 {values[int(0.9 * len(values))]:.1f} "
                     f"max {values[-1]:.1f}")
    worst = collections.Counter(r["module"] for r in measured)
    lines.append("ten worst modules:")
    for name, count in worst.most_common(10):
        sample = next(r for r in measured if r["module"] == name)
        lines.append(f"  {count:3d}  {name:<52s} frame {sample['frame']:3d}"
                     f"  {sample['cause']}")
    return lines


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--corpus", type=Path, default=corpus.CORPUS)
    parser.add_argument("--goals", type=Path, default=GOALS)
    parser.add_argument("--build-dir", type=Path,
                        default=Path("_build/agents/corpus"))
    parser.add_argument("--json", type=Path, default=None)
    arguments = parser.parse_args()
    costs = module_costs(arguments.build_dir)
    rows = [measure(record, arguments.goals, costs)
            for record in expensive(corpus.read(arguments.corpus))]
    if arguments.json:
        arguments.json.write_text(
            "".join(json.dumps(row) + "\n" for row in rows))
    for line in report(rows):
        print(line)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
