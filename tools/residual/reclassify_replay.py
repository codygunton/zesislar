#!/usr/bin/env python3
"""Recompute every replay step from the stored goal texts.

Iteration 2 classified the head of the goal text, which is the hypothesis
context, and recorded the first context line as the goal head. Both come
out of the stored text offline, with no probe re-run: the text holds the
whole goal, rule line included.

The tactic the author applied is re-derived from the module, because the
replay applied the proof's own sentences in order.
"""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

from classify import classify_goal  # noqa: E402
from goals import context_size, conclusion_text  # noqa: E402
from modules import find_proof  # noqa: E402
from sentences import opener_and_steps  # noqa: E402
from signature import signature  # noqa: E402

PROOF_DIR = Path("ZesuSsz/Proofs/WriteSuccess")
REPLAY = Path("ZesuSsz/Evidence/residuals/replay.jsonl")
GOALS = Path("_build/agents/corpus/residuals")
SAMPLE_LINES = 5


def sentences_of(module: str, lemma: str) -> list[str]:
    try:
        proof = find_proof(PROOF_DIR / module, lemma)
    except Exception:
        return []
    return opener_and_steps("\n".join(proof.body))[1]


def step_facts(digests: list[str], goals: Path) -> dict:
    """Class, head, signature, frame size and a sample, per residual goal."""
    classes, heads, signatures, samples, frames, points = [], [], [], [], [], []
    for digest in digests:
        stored = goals / f"{digest}.txt"
        if not stored.exists():
            continue
        text = stored.read_text()
        context, conclusion = conclusion_text(text)
        prediction = classify_goal(text)
        size, memory = context_size(context)
        classes.append(prediction.pred_class)
        heads.append(" ".join(conclusion.split())[:120])
        signatures.append(signature(conclusion))
        samples.append("\n".join(conclusion.split("\n")[:SAMPLE_LINES]))
        frames.append(size)
        points.append(memory)
    return {"classes": classes, "goal_head": heads,
            "signatures": signatures, "samples": samples,
            "frame": frames, "mapsto": points}


def rewrite(records: list[dict], goals: Path) -> list[dict]:
    for record in records:
        steps = sentences_of(record["module"], record["lemma"])
        for step in record["steps"]:
            step.update(step_facts(step.get("goal_sha256", []), goals))
            index = step["index"]
            step["sentence"] = (steps[index - 1] if 0 < index <= len(steps)
                                else "")
    return records


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--replay", type=Path, default=REPLAY)
    parser.add_argument("--goals", type=Path, default=GOALS)
    arguments = parser.parse_args()
    records = [json.loads(line) for line
               in arguments.replay.read_text().split("\n") if line.strip()]
    before = sum(len(s["classes"]) for r in records for s in r["steps"])
    records = rewrite(records, arguments.goals)
    after = sum(len(s["classes"]) for r in records for s in r["steps"])
    arguments.replay.write_text(
        "".join(json.dumps(record) + "\n" for record in records))
    print(f"{len(records)} replays, goals classified {before} -> {after}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
