#!/usr/bin/env python3
"""WP1: where the seconds of one block proof go.

Reads the `timed` probe records and prints one row per lemma. The labels
nest: `phase:run` contains the search loop (`alt:*`) and the finisher
(`fin:*`); `alt:*_zesu_liAStep` contains the Lithium interpreter step
(`li:*`). So the table reports

- intro: `phase:intro`, the introduction phase of `zesu_block`.
- search: the whole `repeat first [ ... ]` loop.
- step: the Lithium interpreter step inside it.
- lithium: `liStep`, inside the step, which is where `liFindInContext` runs.
- asm: `liAAsm`, the instruction semantics inside the step.
- battery: the alternatives of the loop that are not the step; almost all
  of their calls fail, so this is the cost of trying them.
- finisher: every `zesu_finish` entry.
- rest: run seconds the labels do not cover.

The `time` tactical costs about half a millisecond per call, so a lemma
with many interpreter steps reads slower here than it does unlabelled; the
`counted` probe of the same lemma gives the unlabelled seconds.
"""

from __future__ import annotations

import argparse
import collections
import json
import re
from pathlib import Path


def sum_labels(labels: dict, prefix: str) -> float:
    return round(sum(entry["seconds"] for name, entry in labels.items()
                     if name.startswith(prefix)), 2)


def one(name: str, labels: dict) -> float:
    """Seconds of the entry called `name`, whatever its index.

    The legacy automation and the current one order their alternatives
    differently, so a label must be matched by the tactic it names, never by
    the number the generator gave it.
    """
    pattern = re.compile(rf"^(alt|li|lis|fin|phase):\d*_?{re.escape(name)}$")
    return round(sum(entry["seconds"] for label, entry in labels.items()
                     if pattern.match(label)), 2)


def row_of(record: dict, frames: dict, counted: dict) -> dict:
    labels = record.get("labels", {})
    key = (record["module"], record["lemma"])
    run = one("run", labels)
    total = one("block", labels)
    search = sum_labels(labels, "alt:")
    step = one("zesu_liAStep", labels)
    finisher = sum_labels(labels, "fin:")
    return {
        "module": record["module"], "lemma": record["lemma"],
        "frame": frames.get(key, {}).get("frame", ""),
        "mapsto": frames.get(key, {}).get("mapsto", ""),
        "instructions": record.get("instructions", 0),
        "labelled_seconds": record.get("wall", 0.0),
        "plain_seconds": counted.get(key, {}).get("wall", 0.0),
        "intro": round(max(0.0, total - run), 2), "run": run,
        "search": search, "step": step, "battery": round(search - step, 2),
        "lithium": one("liStep", labels), "asm": one("liAAsm", labels),
        "lookup": one("liFindInContext", labels),
        "sidecond": one("liSideCond", labels),
        "finisher": finisher,
        "rest": round(max(0.0, run - search - finisher), 2),
    }


def read(path: Path | None) -> dict:
    if not path or not path.exists():
        return {}
    out = {}
    for line in path.read_text().split("\n"):
        if line.strip():
            record = json.loads(line)
            if record.get("reached_end"):
                out[(record["module"], record["lemma"])] = record
    return out


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--timed", type=Path, required=True)
    parser.add_argument("--frames", type=Path, default=None)
    parser.add_argument("--counted", type=Path, default=None)
    parser.add_argument("--out", type=Path, default=None)
    parser.add_argument("--entries", type=Path, default=None)
    arguments = parser.parse_args()
    frames, counted = read(arguments.frames), read(arguments.counted)
    rows, entries = [], collections.defaultdict(
        lambda: {"seconds": 0.0, "calls": 0, "failures": 0})
    for line in arguments.timed.read_text().split("\n"):
        if not line.strip():
            continue
        record = json.loads(line)
        if not record.get("reached_end"):
            continue
        rows.append(row_of(record, frames, counted))
        for name, entry in record.get("labels", {}).items():
            for field in ("seconds", "calls", "failures"):
                entries[name][field] += entry[field]
    rows.sort(key=lambda row: row["frame"] if row["frame"] != "" else 0)
    print(f"{'frame':>5} {'mp':>3} {'ins':>4} {'plain':>7} {'lbl':>7} "
          f"{'intro':>6} {'search':>7} {'step':>7} {'lith':>7} {'asm':>6} "
          f"{'battery':>7} {'finish':>7} {'look':>6} {'rest':>6}  lemma")
    for row in rows:
        print(f"{row['frame']!s:>5} {row['mapsto']!s:>3} "
              f"{row['instructions']:>4} {row['plain_seconds']:>7.1f} "
              f"{row['labelled_seconds']:>7.1f} {row['intro']:>6.1f} "
              f"{row['search']:>7.1f} {row['step']:>7.1f} "
              f"{row['lithium']:>7.1f} {row['asm']:>6.1f} "
              f"{row['battery']:>7.1f} {row['finisher']:>7.1f} "
              f"{row['lookup']:>6.1f} {row['rest']:>6.1f}  {row['lemma'][:40]}")
    print()
    print("entries by seconds over the profiled lemmas "
          f"({len(rows)} lemmas):")
    for name, entry in sorted(entries.items(),
                              key=lambda kv: -kv[1]["seconds"])[:24]:
        print(f"  {entry['seconds']:9.2f}s {entry['calls']:8d} calls "
              f"{entry['failures']:8d} failed  {name}")
    if arguments.out:
        arguments.out.parent.mkdir(parents=True, exist_ok=True)
        arguments.out.write_text("".join(json.dumps(r) + "\n" for r in rows))
    if arguments.entries:
        arguments.entries.parent.mkdir(parents=True, exist_ok=True)
        arguments.entries.write_text(json.dumps(
            {name: {k: round(v, 3) if isinstance(v, float) else v
                    for k, v in entry.items()}
             for name, entry in sorted(entries.items(),
                                       key=lambda kv: -kv[1]["seconds"])},
            indent=1))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
