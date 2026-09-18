#!/usr/bin/env python3
"""Aggregate the replay records of section 10 E1.

A hand line is *needed* when the automation could not finish the proof
before it. Everything after `closes_at` is not needed. The class of the goal
standing before a needed line is the gap that line fills, so the pair
(class, tactic) names an automation opportunity.
"""

from __future__ import annotations

import argparse
import collections
import json
import statistics
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

REPLAY = Path("ZesuSsz/Evidence/residuals/replay.jsonl")
BUCKETS = [(0.0, "0"), (0.25, "0-25%"), (0.5, "25-50%"),
           (0.75, "50-75%"), (1.0, "75-100%")]


def read(path: Path) -> list[dict]:
    if not Path(path).exists():
        return []
    return [json.loads(line) for line in Path(path).read_text().split("\n")
            if line.strip()]


def replayed(records: list[dict]) -> list[dict]:
    return [r for r in records if r["outcome"] == "replayed"]


def needed_pairs(record: dict) -> list[tuple[str, str]]:
    """(class of the goal it met, tactic) for every needed line of a proof."""
    steps = {step["index"]: step for step in record["steps"]}
    last = record["closes_at"]
    if last is None:
        last = max(steps) if steps else 0
    pairs = []
    for index in range(1, last + 1):
        before = steps.get(index - 1)
        line = steps.get(index)
        if line is None:
            continue
        shape = goal_shape(before)
        pairs.append((shape, line["tactic"]))
    return pairs


def goal_shape(before: dict | None) -> str:
    """The class of the goal a hand line met, or why there was no goal."""
    if before is None:
        return "unseen"
    if before["classes"]:
        return before["classes"][0]
    if before.get("failed"):
        return "error"
    if before.get("closes"):
        return "closed"
    return "unseen"


def fraction_bucket(record: dict) -> str:
    total = record["n_sentences"] - 1
    if record["closes_at"] is None:
        return "never"
    if record["closes_at"] == 0:
        return "0"
    if total <= 0:
        return "0"
    ratio = record["closes_at"] / total
    for edge, name in BUCKETS[1:]:
        if ratio <= edge:
            return name
    return "75-100%"


def report(records: list[dict]) -> list[str]:
    done = replayed(records)
    lines = [f"replays {len(records)}: "
             + " ".join(f"{name} {count}" for name, count in
                        collections.Counter(r["outcome"] for r in records).most_common())]
    if not done:
        return lines
    buckets = collections.Counter(fraction_bucket(r) for r in done)
    order = ["0", "0-25%", "25-50%", "50-75%", "75-100%", "never"]
    lines.append("closes_at / lines: " + " ".join(
        f"{name} {buckets.get(name, 0)}" for name in order))

    closing = [r for r in done if r["closes_at"] is not None]
    saved = sum(max(0, r["n_sentences"] - 1 - r["closes_at"]) for r in closing)
    total_steps = sum(max(0, r["n_sentences"] - 1) for r in done)
    lines.append(f"proofs the automation finishes early {len(closing)}/{len(done)};"
                 f" sentences already unnecessary {saved} of {total_steps}")

    pairs = collections.Counter()
    proofs = collections.defaultdict(set)
    for record in done:
        for shape, tactic in needed_pairs(record):
            pairs[(shape, tactic)] += 1
            proofs[(shape, tactic)].add((record["module"], record["lemma"]))
    lines.append("needed lines by class: " + " ".join(
        f"{name} {count}" for name, count in
        collections.Counter(shape for shape, _ in pairs.elements()).most_common()))
    lines.append("needed lines by tactic: " + " ".join(
        f"{name} {count}" for name, count in
        collections.Counter(tactic for _, tactic in pairs.elements()).most_common(10)))
    lines.append("top (class, tactic) pairs: lines / proofs")
    for (shape, tactic), count in pairs.most_common(20):
        lines.append(f"  {shape:<8s} {tactic:<24s} {count:5d} "
                     f"{len(proofs[(shape, tactic)]):5d}")
    seconds = [r["seconds"] for r in done]
    lines.append(f"replay seconds median {statistics.median(seconds):.1f} "
                 f"p90 {sorted(seconds)[int(0.9 * len(seconds))]:.1f}")
    return lines


def backlog(records: list[dict], limit: int = 25) -> list[str]:
    """The ranked automation backlog, one row per (class, tactic) gap."""
    done = replayed(records)
    pairs = collections.Counter()
    proofs = collections.defaultdict(set)
    heads = collections.defaultdict(collections.Counter)
    for record in done:
        steps = {step["index"]: step for step in record["steps"]}
        for index, (shape, tactic) in enumerate(needed_pairs(record), start=1):
            pairs[(shape, tactic)] += 1
            proofs[(shape, tactic)].add((record["module"], record["lemma"]))
            before = steps.get(index - 1)
            if before and before["goal_head"]:
                heads[(shape, tactic)][before["goal_head"][0][:60]] += 1
    rows = ["| rank | class | hand line | proofs | lines | most common goal head |",
            "| --- | --- | --- | --- | --- | --- |"]
    for rank, ((shape, tactic), count) in enumerate(pairs.most_common(limit), 1):
        head = heads[(shape, tactic)].most_common(1)
        rows.append(f"| {rank} | {shape} | `{tactic}` | "
                    f"{len(proofs[(shape, tactic)])} | {count} | "
                    f"`{head[0][0] if head else '-'}` |")
    return rows


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--replay", type=Path, default=REPLAY)
    parser.add_argument("--backlog", action="store_true")
    parser.add_argument("--modules", type=Path, default=None)
    arguments = parser.parse_args()
    records = read(arguments.replay)
    if arguments.modules:
        names = {Path(n).name for n in arguments.modules.read_text().split()}
        records = [r for r in records if r["module"] in names]
    for line in (backlog(records) if arguments.backlog else report(records)):
        print(line)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
