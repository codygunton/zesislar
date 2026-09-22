#!/usr/bin/env python3
"""Compare two `counted` runs of the same lemma set, lemma by lemma.

The benchmark median is a weak instrument for an automation change: most of
its lemmas are small, and most of a small probe's seconds are the module
text it compiles before the automation starts. A paired comparison of the
same lemmas on the same machine answers the question the acceptance asks --
did the automation get faster -- without that noise.

`zesu_run` seconds come from the timer the automation already prints, so
they exclude the module compile entirely.
"""

from __future__ import annotations

import argparse
import json
import statistics
from pathlib import Path


def read(path: Path) -> dict:
    out = {}
    for line in path.read_text().split("\n"):
        if line.strip():
            record = json.loads(line)
            out[(record["module"], record["lemma"])] = record
    return out


def summarize(name: str, values: list[float]) -> str:
    if not values:
        return f"{name}: nothing measured"
    ordered = sorted(values)
    return (f"{name}: n {len(ordered)}  median {statistics.median(ordered):.2f}"
            f"  p90 {ordered[int(0.9 * len(ordered))]:.2f}"
            f"  total {sum(ordered):.0f}")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--before", type=Path, required=True)
    parser.add_argument("--after", type=Path, required=True)
    parser.add_argument("--out", type=Path, default=None)
    arguments = parser.parse_args()
    before, after = read(arguments.before), read(arguments.after)
    shared = sorted(set(before) & set(after))
    rows = []
    for key in shared:
        old, new = before[key], after[key]
        rows.append({
            "module": key[0], "lemma": key[1],
            "before_seconds": old.get("wall", 0.0),
            "after_seconds": new.get("wall", 0.0),
            "before_run": round(sum(old.get("zesu_run_seconds", [])), 3),
            "after_run": round(sum(new.get("zesu_run_seconds", [])), 3),
            "before_end": bool(old.get("reached_end")),
            "after_end": bool(new.get("reached_end")),
            "before_instructions": old.get("instructions", 0),
            "after_instructions": new.get("instructions", 0)})
    both = [r for r in rows if r["before_end"] and r["after_end"]]
    print(f"lemmas in both runs: {len(rows)}; finished in both: {len(both)}")
    print(f"finished before only: "
          f"{sum(1 for r in rows if r['before_end'] and not r['after_end'])}; "
          f"after only: "
          f"{sum(1 for r in rows if r['after_end'] and not r['before_end'])}")
    print(summarize("probe seconds before", [r["before_seconds"] for r in both]))
    print(summarize("probe seconds after ", [r["after_seconds"] for r in both]))
    print(summarize("zesu_run seconds before",
                    [r["before_run"] for r in both]))
    print(summarize("zesu_run seconds after ",
                    [r["after_run"] for r in both]))
    run = [r for r in both if r["before_run"] > 0]
    ratios = sorted(r["after_run"] / r["before_run"] for r in run)
    if ratios:
        print(f"paired zesu_run ratio over {len(ratios)} lemmas: "
              f"median {statistics.median(ratios):.3f}  "
              f"p10 {ratios[len(ratios) // 10]:.3f}  "
              f"p90 {ratios[9 * len(ratios) // 10]:.3f}  "
              f"slower than before: "
              f"{sum(1 for v in ratios if v > 1.05)}")
    heavy = [r for r in run if r["before_run"] >= 10]
    if heavy:
        print(summarize("  of the ones over 10 s before: before",
                        [r["before_run"] for r in heavy]))
        print(summarize("  of the ones over 10 s before: after ",
                        [r["after_run"] for r in heavy]))
    changed = [r for r in rows
               if r["before_instructions"] != r["after_instructions"]]
    print(f"instruction count changed for {len(changed)} lemmas")
    if arguments.out:
        arguments.out.parent.mkdir(parents=True, exist_ok=True)
        arguments.out.write_text("".join(json.dumps(r) + "\n" for r in rows))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
