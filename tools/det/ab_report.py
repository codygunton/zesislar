#!/usr/bin/env python3
"""Report an interleaved A/B run, paired lemma by lemma."""

from __future__ import annotations

import argparse
import json
import statistics
from pathlib import Path


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--records", type=Path, required=True)
    parser.add_argument("--field", default="run_seconds",
                        choices=["run_seconds", "wall"])
    arguments = parser.parse_args()
    arms: dict[str, dict] = {"before": {}, "after": {}}
    for line in arguments.records.read_text().split("\n"):
        if not line.strip():
            continue
        record = json.loads(line)
        arms[record["arm"]][(record["module"], record["lemma"])] = record
    shared = sorted(set(arms["before"]) & set(arms["after"]))
    both = [k for k in shared
            if arms["before"][k].get("reached_end")
            and arms["after"][k].get("reached_end")]
    print(f"paired lemmas {len(shared)}; finished in both arms {len(both)}")
    print("finished before only "
          f"{sum(1 for k in shared if arms['before'][k].get('reached_end') and not arms['after'][k].get('reached_end'))}"
          "; after only "
          f"{sum(1 for k in shared if arms['after'][k].get('reached_end') and not arms['before'][k].get('reached_end'))}")
    field = arguments.field
    before = [arms["before"][k][field] for k in both]
    after = [arms["after"][k][field] for k in both]
    print(f"{field}: median {statistics.median(before):.2f} -> "
          f"{statistics.median(after):.2f}; total {sum(before):.0f} -> "
          f"{sum(after):.0f} ({100 * (sum(after) / max(sum(before), 1e-9) - 1):+.1f}%)")
    pairs = [(arms["before"][k][field], arms["after"][k][field])
             for k in both if arms["before"][k][field] > 0]
    ratios = sorted(a / b for b, a in pairs)
    if ratios:
        print(f"paired ratio over {len(ratios)}: median "
              f"{statistics.median(ratios):.3f}  p10 {ratios[len(ratios)//10]:.3f}"
              f"  p90 {ratios[9*len(ratios)//10]:.3f}")
    for low, high in [(0, 1), (1, 3), (3, 10), (10, 30), (30, 100),
                      (100, 10 ** 9)]:
        chosen = [(b, a) for b, a in pairs if low <= b < high]
        if len(chosen) < 5:
            continue
        band = sorted(a / b for b, a in chosen)
        print(f"  before {low:4}-{high:5}s n={len(chosen):4d} median ratio "
              f"{statistics.median(band):.3f}  total "
              f"{sum(b for b, _ in chosen):7.0f} -> "
              f"{sum(a for _, a in chosen):7.0f}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
