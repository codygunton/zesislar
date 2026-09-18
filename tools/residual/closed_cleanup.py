#!/usr/bin/env python3
"""List the hand proofs that the block automation now closes on its own.

Section 9 item 3: a list, nothing else. The compliance orchestrator replaces
those proof bodies as a logged batch. This plan never edits a proof.
"""

from __future__ import annotations

import argparse
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

import corpus  # noqa: E402

SECONDS_CAP = 60.0
HEADER = ("# module lemma hand_lines probe_seconds\n"
          "# `zesu_block.` alone closes each of these proofs, in at most "
          f"{SECONDS_CAP:.0f} s.\n"
          "# A list only. Replacing the bodies belongs to compliance plan "
          "7.6.1.\n")


def rows(records: list[dict], cap: float = SECONDS_CAP) -> list[str]:
    closed = [r for r in records
              if r.get("outcome") == "closed" and float(r.get("seconds", 0)) <= cap]
    closed.sort(key=lambda r: (-len([line for line in r.get("label_lines", [])
                                     if line.strip()]), r["module"], r["lemma"]))
    return [f"{r['module']} {r['lemma']} "
            f"{len([line for line in r.get('label_lines', []) if line.strip()])} "
            f"{float(r['seconds']):.1f}" for r in closed]


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--corpus", type=Path, default=corpus.CORPUS)
    parser.add_argument("--output", type=Path,
                        default=Path("ZesuSsz/Evidence/residuals/closed_cleanup.txt"))
    parser.add_argument("--seconds", type=float, default=SECONDS_CAP)
    arguments = parser.parse_args()
    lines = rows(corpus.read(arguments.corpus), arguments.seconds)
    arguments.output.write_text(HEADER + "\n".join(lines) + "\n")
    print(f"{len(lines)} proofs listed in {arguments.output}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
