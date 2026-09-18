#!/usr/bin/env python3
"""Probe one lemma and print what the automation leaves, for a human.

This is what a compliance agent runs when its proof stops: one command, the
cost, the class, and the first lines of the goal. It never edits the proof.
"""

from __future__ import annotations

import argparse
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

from capture import capture  # noqa: E402
from classify import classify  # noqa: E402

PROOF_DIR = Path("ZesuSsz/Proofs/WriteSuccess")
GOAL_LINES = 30


def resolve(module: str) -> Path:
    path = Path(module)
    return path if path.exists() else PROOF_DIR / path.name


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("module")
    parser.add_argument("lemma")
    parser.add_argument("--build-dir", type=Path,
                        default=Path("_build/agents/corpus"))
    parser.add_argument("--scratch", type=Path,
                        default=Path("tools/coqc_scratch.sh"))
    parser.add_argument("--lines", type=int, default=GOAL_LINES)
    arguments = parser.parse_args()

    module = resolve(arguments.module)
    goal_dir = arguments.build_dir / "residuals"
    result = capture(module, arguments.lemma, arguments.build_dir,
                     arguments.scratch, goal_dir / "probes")
    prediction = classify(result.goal_text,
                          "residual" if result.goal_text else result.outcome)
    if result.goal_sha256:
        goal_dir.mkdir(parents=True, exist_ok=True)
        (goal_dir / f"{result.goal_sha256}.txt").write_text(result.full_goal_text)

    print(f"lemma     {module.name}:{arguments.lemma}")
    print(f"outcome   {result.outcome}"
          + (f" ({result.error_kind})" if result.error_kind else ""))
    print(f"seconds   {result.seconds:.1f}   rss {result.rss_mib} MiB"
          f"   goals {result.goal_count}")
    print(f"class     {prediction.pred_class}"
          f"   head {prediction.detail.get('head', '-')}")
    if result.goal_sha256:
        print(f"full goal {goal_dir / (result.goal_sha256 + '.txt')}")
    print("-" * 72)
    body = result.goal_text or "\n".join(result.error_lines)
    for line in body.split("\n")[:arguments.lines]:
        print(line)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
