#!/usr/bin/env python3
"""The segment table and the residual classes, from the records on disk.

Every tool on this branch writes JSON Lines with one record per lemma, so
a report is a join, not a new measurement. This reads every `.jsonl`
under the evidence directory, keeps the newest record for each lemma, and
prints two tables:

- the segment table: hand-written lines before and after, whether the
  segment closes, and the class and signature of its first stall;
- the residual classes: how many segments each class still blocks, which
  is the order the tickets are worked in.

Nothing here compiles anything. Run it after a probe batch, or to answer
"where are we" without paying for a build.
"""

from __future__ import annotations

import argparse
import json
from collections import defaultdict
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "residual"))
from classify import VERSION as CLASSIFIER  # noqa: E402

EVIDENCE = Path("ZesuSsz/Evidence/det")
MERGED_SET = EVIDENCE / "boundary_set.txt"
OPEN_SET = EVIDENCE / "open_segments.json"
ROWS = EVIDENCE / "rows.json"


def segments() -> list[str]:
    """The seven: four merged, three open."""
    names: list[str] = []
    if MERGED_SET.exists():
        names += [line.split(":")[1] for line in
                  MERGED_SET.read_text().split("\n") if line.count(":") >= 2]
    if OPEN_SET.exists():
        names += [record["name"] for record in
                  json.loads(OPEN_SET.read_text())]
    return names


def records(directory: Path) -> list[tuple[float, dict]]:
    out: list[tuple[float, dict]] = []
    for path in sorted(directory.rglob("*.jsonl")):
        when = path.stat().st_mtime
        for line in path.read_text().split("\n"):
            line = line.strip()
            if not line.startswith("{"):
                continue
            try:
                record = json.loads(line)
            except json.JSONDecodeError:
                continue
            record["source_file"] = str(path)
            out.append((when, record))
    # Oldest first. `newest_by_lemma` merges a lemma's records and keeps
    # the newest value of each field, and it skips a record older than
    # the one it holds. Iterating in filename order therefore loses a
    # field whenever an older file sorts after a newer one: adding
    # `tail_hops.jsonl` dropped the hand-line column for two segments
    # that way. Sorting by time makes the join order-independent.
    return sorted(out, key=lambda pair: pair[0])


def newest_by_lemma(rows: list[tuple[float, dict]]) -> dict[str, dict]:
    latest: dict[str, tuple[float, dict]] = {}
    for when, record in rows:
        lemma = record.get("lemma")
        if not lemma:
            continue
        keep = latest.get(lemma)
        if keep is None or when >= keep[0]:
            merged = dict(keep[1]) if keep else {}
            merged.update({k: v for k, v in record.items() if v is not None})
            latest[lemma] = (when, merged)
    return {lemma: record for lemma, (_, record) in latest.items()}


def row_table() -> list[str]:
    """The bundle's ten rows, from the record the worker keeps.

    The states are a judgement, not a measurement, so they live in a file
    that is edited when a row moves rather than being guessed from the
    tree. Keeping them here means every report prints the same table.
    """
    if not ROWS.exists():
        return ["(no row record)"]
    lines = ["| # | item | state | left to do |", "|---|---|---|---|"]
    for row in json.loads(ROWS.read_text()):
        lines.append(f"| {row['row']} | {row['item']} | {row['state']} | "
                     f"{row['left'] or '-'} |")
    return lines


def segment_table(by_lemma: dict[str, dict], names: list[str]) -> list[str]:
    header = ("| segment | hand lines before | after | closes | "
              "stall class | signature |")
    lines = [header, "|---|---|---|---|---|---|"]
    for lemma in names:
        record = by_lemma.get(lemma, {})
        before = record.get("before", record.get("hand_lines_before", ""))
        closes = record.get("outcome") == "reached" or record.get("compiled")
        after = record.get("after", record.get("hand_lines_after", ""))
        lines.append(
            f"| {lemma} | {before} | {after if closes else '-'} | "
            f"{'yes' if closes else 'no'} | {record.get('pred_class', '')} | "
            f"{record.get('signature', '')} |")
    return lines


def class_table(by_lemma: dict[str, dict], names: list[str]) -> list[str]:
    blocked: dict[str, set[str]] = defaultdict(set)
    for lemma in names:
        record = by_lemma.get(lemma, {})
        if record.get("outcome") == "stalled" and record.get("pred_class"):
            blocked[record["pred_class"]].add(lemma)
    lines = ["| class | segments blocked | segments |", "|---|---|---|"]
    for name in sorted(blocked, key=lambda k: (-len(blocked[k]), k)):
        members = ", ".join(sorted(blocked[name]))
        lines.append(f"| {name} | {len(blocked[name])} | {members} |")
    if len(lines) == 2:
        lines.append("| - | 0 | no stalled segment on record |")
    return lines


def classifier_line(by_lemma: dict[str, dict], names: list[str]) -> str:
    """The classifier versions the records were classified with."""
    versions = sorted({str(by_lemma[lemma].get("classifier", "1"))
                       for lemma in names if lemma in by_lemma})
    return (f"classifier v{', v'.join(versions) or '-'} (records); "
            f"current v{CLASSIFIER}")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--evidence", type=Path, default=EVIDENCE)
    parser.add_argument("--out", type=Path, default=None)
    arguments = parser.parse_args()
    by_lemma = newest_by_lemma(records(arguments.evidence))
    names = segments()
    text = "\n".join(["## The bundle's ten rows", ""] + row_table()
                     + ["", "## Segments", ""] + segment_table(by_lemma, names)
                     + ["", "## Residual classes still blocking a segment", "",
                        classifier_line(by_lemma, names), ""]
                     + class_table(by_lemma, names) + [""])
    print(text)
    if arguments.out:
        arguments.out.parent.mkdir(parents=True, exist_ok=True)
        arguments.out.write_text(text)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
