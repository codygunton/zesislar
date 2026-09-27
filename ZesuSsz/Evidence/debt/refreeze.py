"""Re-freeze the benchmark and measurement sets before the tier-1 deletion.

Lead's ruling (PLAN_TECH_DEBT_SWEEP section 7, step 1): a set keeps the
population rule set v2 can act on, the modules that import
`ZesuSsz.Automation.All`, minus every row whose module tier 1 deletes. The
three open segments join the benchmark as their own set,
`benchmark_set_segments.txt`, because they exist only as generator specs
(`det/open_segments.json`) and the benchmark harness probes modules that
are in the tree. `make gen-segment` probes them.

Rewrites the sets in place and prints one line per set: before, kept,
dropped as not `All`, dropped as removed, and rows whose module is gone.
"""

import argparse
import json
from pathlib import Path

PROOFS = "ZesuSsz/Proofs/WriteSuccess/"
SETS = ["ZesuSsz/Evidence/residuals/benchmark_set.txt",
        "ZesuSsz/Evidence/residuals/benchmark_set_rule15.txt",
        *sorted(str(p) for p in Path("ZesuSsz/Evidence/det").glob("*_set.txt")),
        "ZesuSsz/Evidence/det/expensive_no_context.txt"]
SEGMENTS = "ZesuSsz/Evidence/residuals/benchmark_set_segments.txt"


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--modules", required=True, help="inventory.py output")
    args = parser.parse_args()
    records = json.loads(Path(args.modules).read_text())

    for name in SETS:
        path = Path(name)
        rows = [ln for ln in path.read_text().splitlines() if ln.strip()]
        kept, not_all, removed, missing = [], 0, 0, 0
        for row in rows:
            module = PROOFS + row.split(":")[0]
            rec = records.get(module)
            if rec is None:
                missing += 1
            elif rec["class"] == "remove now":
                removed += 1
            elif rec["rule_set"] != "All":
                not_all += 1
            else:
                kept.append(row)
        path.write_text("".join(r + "\n" for r in kept))
        print(f"{name}: {len(rows)} -> {len(kept)} "
              f"(not All {not_all}, removed {removed}, missing {missing})")

    specs = json.loads(Path("ZesuSsz/Evidence/det/open_segments.json").read_text())
    lines = [f"{s['name']}:{s['entry']}:{s['exit']}" for s in specs]
    Path(SEGMENTS).write_text("".join(ln + "\n" for ln in lines))
    print(f"{SEGMENTS}: {len(lines)} open segments")


if __name__ == "__main__":
    main()
