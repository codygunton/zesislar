#!/usr/bin/env python3
"""Apply the re-probe policy to a stored benchmark arm.

    python3 tools/residual/reprobe.py f425f7ea4f7b-v2 \
        --import ZesuSsz.Automation.Sets.v2

Every lemma whose stored outcome is an error or a timeout is probed again,
alone, in the arm's immutable tree, and the alone result becomes the
stored outcome, flagged `reprobed`, with the batch result kept under
`batch`. `benchmark.py` does this itself for every new arm; this tool is
for an arm stored before the policy (lead, 2026-09-23).

The arm must be probed with the imports it was measured with. An arm
stored since the policy records them; an older one needs `--import`.
"""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

import benchmark  # noqa: E402

ROOT = Path(__file__).resolve().parents[2]


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("arm", help="stored arm name, e.g. f425f7ea4f7b-v2")
    parser.add_argument("--import", dest="imports", action="append",
                        default=None)
    parser.add_argument("--seconds", type=int, default=None)
    arguments = parser.parse_args()

    path = ROOT / benchmark.RESULT_DIR / f"{arguments.arm}.json"
    stored = json.loads(path.read_text())
    imports = tuple(arguments.imports if arguments.imports is not None
                    else stored.get("imports", []))
    seconds = arguments.seconds or stored.get("seconds", 300)
    root = benchmark.source_tree(
        ROOT, stored["automation"],
        without_tests=benchmark.TESTS_DIR in stored.get("excluded", []))
    if not (root / ".arm-commit").exists():
        raise SystemExit(f"arm tree {root} is not built; run the arm first")
    already = [row for row in stored["rows"] if row.get("reprobed")]
    if already:
        raise SystemExit(f"{arguments.arm}: {len(already)} rows already reprobed")
    rows = benchmark.reprobe_alone(root, stored["rows"], seconds, imports)
    before = stored["summary"]
    stored.update({"rows": rows, "summary": benchmark.summary(rows),
                   "imports": list(imports), "seconds": seconds})
    path.write_text(json.dumps(stored))
    print(f"{arguments.arm}: {benchmark.reprobe_line(rows)}")
    print("outcomes before " + json.dumps(before["outcomes"], sort_keys=True))
    print("outcomes after  " + json.dumps(stored["summary"]["outcomes"],
                                          sort_keys=True))
    return 0


if __name__ == "__main__":
    sys.exit(main())
