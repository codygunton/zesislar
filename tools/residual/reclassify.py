#!/usr/bin/env python3
"""Reclassify a stored benchmark arm offline, from its stored goal texts.

    python3 tools/residual/reclassify.py ccf505e81f85 ccf505e81f85-rule15 --check
    python3 tools/residual/reclassify.py ccf505e81f85 ccf505e81f85-rule15

An arm stores, per lemma, the SHA-256 of its full goal text. The texts sit
in content-addressed goal directories (`<sha>.txt`), and any arm's
directory can answer for a goal another arm produced. The benchmark
classified `full[:GOAL_TEXT_HEAD]`, so this does the same: with an
unchanged classifier a reclassification reproduces every stored class,
which `--check` demonstrates before any file is written.

Only `pred_class` and the class table change. Outcomes, seconds,
signatures, and closed counts are copied as they are. The arm records the
classifier version it was classified with (`classify.VERSION`).
"""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

import classify  # noqa: E402
from capture import GOAL_TEXT_HEAD  # noqa: E402
from benchmark import RESULT_DIR, summary  # noqa: E402

ROOT = Path(__file__).resolve().parents[2]
GOAL_DIRS = ["_build/agents/det/residuals", "_build/agents/corpus/residuals",
             "_build/agents/bench/*/_build/residuals"]


def goal_dirs(extra: list[Path]) -> list[Path]:
    found = list(extra)
    for pattern in GOAL_DIRS:
        found += sorted(ROOT.glob(pattern))
    return [path for path in found if path.is_dir()]


def goal_text(digest: str, directories: list[Path]) -> str | None:
    for directory in directories:
        path = directory / f"{digest}.txt"
        if path.exists():
            return path.read_text()
    return None


def reclassify(rows: list[dict], directories: list[Path]) -> tuple[list[dict], list[str]]:
    """New rows, and the lemmas whose goal text was not found."""
    missing, result = [], []
    for row in rows:
        row = dict(row)
        digest = row.get("goal_sha256")
        if digest:
            text = goal_text(digest, directories)
            if text is None:
                missing.append(f"{row['module']}:{row['lemma']}")
            else:
                head = text[:GOAL_TEXT_HEAD]
                row["pred_class"] = classify.classify(
                    head, "residual" if head else row["outcome"]).pred_class
        result.append(row)
    return result, missing


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("arms", nargs="+", help="stored arm names, e.g. ccf505e81f85")
    parser.add_argument("--goal-dir", type=Path, action="append", default=[])
    parser.add_argument("--check", action="store_true",
                        help="report changes, write nothing")
    arguments = parser.parse_args()
    directories = goal_dirs(arguments.goal_dir)
    status = 0
    for arm in arguments.arms:
        path = ROOT / RESULT_DIR / f"{arm}.json"
        stored = json.loads(path.read_text())
        rows, missing = reclassify(stored["rows"], directories)
        changed = [(old, new) for old, new in zip(stored["rows"], rows)
                   if old["pred_class"] != new["pred_class"]]
        print(f"{arm}: classifier {stored.get('classifier', '1')} -> "
              f"{classify.VERSION}; {len(changed)} of {len(rows)} classes "
              f"changed; {len(missing)} goal texts missing")
        for old, new in changed:
            print(f"  {old['module']}:{old['lemma']}: "
                  f"{old['pred_class']} -> {new['pred_class']}")
        for name in missing:
            print(f"  missing: {name}")
        if missing:
            status = 1
            continue
        before, after = stored["summary"], summary(rows)
        assert before["outcomes"] == after["outcomes"]
        assert before["closed_fraction"] == after["closed_fraction"]
        if not arguments.check:
            stored.update({"rows": rows, "summary": after,
                           "classifier": classify.VERSION})
            path.write_text(json.dumps(stored))
    return status


if __name__ == "__main__":
    sys.exit(main())
