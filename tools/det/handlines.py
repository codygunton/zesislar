#!/usr/bin/env python3
"""Hand-written proof lines per segment, before and after.

The optimization target is the Rocq an agent has to write, not the seconds
a machine spends. This counts, for each lemma, the sentences of its proof
body that are not the block automation call itself, at two commits.
"""

from __future__ import annotations

import argparse
import json
import subprocess
import sys
import tempfile
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "residual"))

from modules import find_proof, parse_module  # noqa: E402

PROOF_DIR = Path("ZesuSsz/Proofs/WriteSuccess")


def at_commit(commit: str, path: str) -> str | None:
    done = subprocess.run(["git", "show", f"{commit}:{path}"],
                          capture_output=True, text=True)
    return done.stdout if done.returncode == 0 else None


def hand_lines(text: str, lemma: str) -> int | None:
    with tempfile.NamedTemporaryFile("w", suffix=".v", delete=False) as handle:
        handle.write(text)
        temporary = Path(handle.name)
    try:
        return len(find_proof(temporary, lemma).hand_lines)
    except KeyError:
        return None
    finally:
        temporary.unlink(missing_ok=True)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--set", type=Path, required=True,
                        help="one MODULE:LEMMA[:anything] per line")
    parser.add_argument("--before", required=True)
    parser.add_argument("--after", default="HEAD")
    parser.add_argument("--out", type=Path, default=None)
    arguments = parser.parse_args()
    rows, total_before, total_after = [], 0, 0
    for line in arguments.set.read_text().split("\n"):
        if ":" not in line:
            continue
        module, lemma = line.split(":")[:2]
        path = str(PROOF_DIR / Path(module).name)
        counts = []
        for commit in (arguments.before, arguments.after):
            text = at_commit(commit, path)
            counts.append(hand_lines(text, lemma) if text else None)
        before, after = counts
        rows.append({"module": Path(module).name, "lemma": lemma,
                     "before": before, "after": after,
                     "removed": (before - after)
                     if before is not None and after is not None else None})
        total_before += before or 0
        total_after += after or 0
    width = max((len(r["lemma"]) for r in rows), default= 10)
    print(f"{'before':>6} {'after':>6} {'removed':>8}  lemma")
    for row in rows:
        print(f"{row['before']!s:>6} {row['after']!s:>6} "
              f"{row['removed']!s:>8}  {row['lemma'][:width]}")
    print(f"{total_before:>6} {total_after:>6} "
          f"{total_before - total_after:>8}  TOTAL over {len(rows)} lemmas")
    if arguments.out:
        arguments.out.parent.mkdir(parents=True, exist_ok=True)
        arguments.out.write_text("".join(json.dumps(r) + "\n" for r in rows))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
