#!/usr/bin/env python3
"""Split the `error` steps of the replay by the message the automation gave.

Section 12 item 1. `error` meant only "the automation neither closed the
goal nor printed a residual". The message probe says why, and the answers
fall into a few kinds with different remedies.
"""

from __future__ import annotations

import argparse
import collections
import json
import re
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

from replay_report import goal_shape, read, replayed  # noqa: E402

MESSAGES = Path("ZesuSsz/Evidence/residuals/messages.jsonl")
REPLAY = Path("ZesuSsz/Evidence/residuals/replay.jsonl")
KINDS = [
    ("budget exceeded", re.compile(r"tclTIMEOUT|Tactic timeout")),
    ("pure goal, iStartProof refused",
     re.compile(r"iStartProof: not a BI assertion")),
    ("no applicable Lithium rule", re.compile(r"No applicable tactic|liStep")),
    ("unification failed", re.compile(r"Unable to unify|cannot unify")),
    ("no such goal", re.compile(r"No such goal|No more goals")),
    ("other tactic failure", re.compile(r"Tactic failure")),
]
SHELVED = re.compile(r"SHELVED_SIDECOND")


def kind_of(message: str) -> str:
    """The kind of stop, from the message the automation gave.

    An empty message means the probe reported `RAN`: the automation
    succeeded as a tactic at that state, and the replay recorded `failed`
    only because it could not then print the residual.
    """
    if not message.strip():
        return "ran, residual not printable"
    for name, pattern in KINDS:
        if pattern.search(message):
            return name
    return "unrecognised"


def error_steps(records: list[dict]) -> list[tuple[str, str, int]]:
    """Every needed step whose preceding state was an automation error."""
    found = []
    for record in replayed(records):
        steps = {step["index"]: step for step in record["steps"]}
        last = record["closes_at"]
        if last is None:
            last = max(steps, default=0)
        for index in range(1, last + 1):
            if index in steps and goal_shape(steps.get(index - 1)) == "error":
                found.append((record["module"], record["lemma"], index - 1))
    return found


def report(replay: list[dict], messages: list[dict]) -> list[str]:
    by_proof = {(r["module"], r["lemma"]): (r.get("messages") or {})
                for r in messages}
    steps = error_steps(replay)
    kinds = collections.Counter()
    missing = 0
    pure_shelved = 0
    for module, lemma, index in steps:
        text = by_proof.get((module, lemma), {}).get(str(index))
        if text is None:
            missing += 1
            continue
        kinds[kind_of(text)] += 1
        if SHELVED.search(text):
            pure_shelved += 1
    lines = [f"error steps {len(steps)}; message probes cover "
             f"{len(steps) - missing}, {missing} not yet probed",
             "by message kind: " + " ".join(
                 f"{name} {count}" for name, count in kinds.most_common())]
    if pure_shelved:
        lines.append(f"of the pure goals, {pure_shelved} are shelved side"
                     f" conditions (`SHELVED_SIDECOND`)")
    samples = collections.Counter()
    for record in messages:
        for text in (record.get("messages") or {}).values():
            if text:
                samples[re.sub(r"\d+", "N", text)[:110]] += 1
    lines.append("ten most frequent messages:")
    for text, count in samples.most_common(10):
        lines.append(f"  {count:5d}  {text}")
    return lines


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--replay", type=Path, default=REPLAY)
    parser.add_argument("--messages", type=Path, default=MESSAGES)
    arguments = parser.parse_args()
    messages = (read(arguments.messages) if arguments.messages.exists()
                else [])
    for line in report(read(arguments.replay), messages):
        print(line)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
