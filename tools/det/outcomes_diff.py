#!/usr/bin/env python3
"""Two benchmark arms, lemma by lemma: what changed and what did not.

Row 6 of the bundle owes "zero changed outcomes on v1 modules". A
summary cannot show that: two arms can agree on every count and still
disagree on which lemma is in which row. So this compares the stored
arms by lemma name and reports four numbers -- outcome changes, class
changes, signature changes, and lemmas present in one arm only -- and
names every lemma behind the first three.

`ZesuSsz/Evidence/residuals/benchmark/<sha12>[-<name>].json` is what
`tools/residual/benchmark.py` writes, and either side may be named by
that file or by its stem.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path

RESULTS = Path("ZesuSsz/Evidence/residuals/benchmark")


def rows_of(name: str) -> dict[str, dict]:
    path = Path(name)
    if not path.exists():
        path = RESULTS / (name if name.endswith(".json") else f"{name}.json")
    if not path.exists():
        raise SystemExit(f"no arm on record at {path}")
    return {f"{row['module']}:{row['lemma']}": row
            for row in json.loads(path.read_text())["rows"]}


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("before")
    parser.add_argument("after")
    parser.add_argument("--field", action="append", default=None,
                        help="fields to compare (default outcome, "
                             "pred_class, signature)")
    parser.add_argument("--quiet", action="store_true",
                        help="counts only, no per-lemma lines")
    arguments = parser.parse_args()
    fields = arguments.field or ["outcome", "pred_class", "signature"]

    before, after = rows_of(arguments.before), rows_of(arguments.after)
    shared = sorted(set(before) & set(after))
    only_before = sorted(set(before) - set(after))
    only_after = sorted(set(after) - set(before))

    print(f"{arguments.before} -> {arguments.after}: "
          f"{len(shared)} lemmas in both, {len(only_before)} dropped, "
          f"{len(only_after)} added")
    changed = 0
    for field in fields:
        moved = [key for key in shared
                 if before[key].get(field) != after[key].get(field)]
        changed += len(moved)
        print(f"{field}: {len(moved)} changed of {len(shared)}")
        if not arguments.quiet:
            for key in moved:
                print(f"  {key}: {before[key].get(field)!r} -> "
                      f"{after[key].get(field)!r}")
    for key in only_before:
        print(f"  dropped: {key}")
    for key in only_after:
        print(f"  added: {key}")
    return 0 if changed == 0 and not only_before and not only_after else 1


if __name__ == "__main__":
    raise SystemExit(main())
