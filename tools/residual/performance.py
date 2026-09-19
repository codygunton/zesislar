#!/usr/bin/env python3
"""E2: why the expensive probes are expensive.

Three causes look the same from outside: a frame too large to carry, a
search that blows up on few conjuncts, and a finisher that costs more than
the search. The entry predicate of the lemma separates the first from the
other two, and the `zesu_run` timings separate those.
"""

from __future__ import annotations

import argparse
import collections
import json
import re
import statistics
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

import corpus  # noqa: E402
from classify import separated  # noqa: E402
from modules import find_proof  # noqa: E402

PROOF_DIR = Path("ZesuSsz/Proofs/WriteSuccess")
SLOW_SECONDS = 120.0
WIDE_FRAME = 12
INSTR_BODY = re.compile(r"instr_body\s+(?P<address>0x[0-9a-fA-F]+|\d+)")
MAPSTO = re.compile(r"↦ₘ|↦ᵣ")


def statement(module: Path, lemma: str) -> str:
    proof = find_proof(module, lemma)
    lines = module.read_text().split("\n")
    return "\n".join(lines[proof.declaration_line:proof.proof_line])


def entry_predicate(text: str) -> str:
    """The spec `instr_body` receives, as a balanced term.

    Everything after the address up to the matching close paren. Taking the
    rest of the statement instead would count the conjuncts of the frame and
    of the postcondition together.
    """
    found = INSTR_BODY.search(text)
    if found is None:
        return text
    rest = text[found.end():].lstrip()
    if not rest.startswith("("):
        return rest.split("\n")[0]
    depth = 0
    for index, character in enumerate(rest):
        if character == "(":
            depth += 1
        elif character == ")":
            depth -= 1
            if depth == 0:
                return rest[1:index]
    return rest


def conjuncts(text: str) -> int:
    """Top-level separating conjuncts of the entry predicate."""
    count = 1
    depth = 0
    index = 0
    while index < len(text):
        character = text[index]
        if text.startswith("↦ₘ∗", index):
            index += 3
            continue
        if character in "([{⌜⎡":
            depth += 1
        elif character in ")]}⌝⎤":
            depth = max(0, depth - 1)
        elif character == "∗" and depth == 0:
            count += 1
        index += 1
    return count


def cause(frame: int, seconds: float, run_seconds: list[float]) -> str:
    """Frame size, search blowup, or finisher cost."""
    if frame > WIDE_FRAME:
        return "frame size"
    inside = sum(run_seconds)
    if inside and inside < 0.5 * seconds:
        return "finisher cost"
    return "search blowup"


def measure(record: dict) -> dict:
    module = PROOF_DIR / record["module"]
    try:
        text = statement(module, record["lemma"])
    except Exception:
        text = ""
    entry = entry_predicate(text)
    run_seconds = [float(value) for value in record.get("zesu_run_seconds", [])]
    frame = conjuncts(entry)
    return {"module": record["module"], "lemma": record["lemma"],
            "outcome": record["outcome"],
            "seconds": float(record.get("seconds", 0.0)),
            "rss_mib": record.get("rss_mib", 0),
            "conjuncts": frame,
            "mapsto": len(MAPSTO.findall(entry)),
            "instructions": len(run_seconds),
            "zesu_run_total": round(sum(run_seconds), 2),
            "seconds_per_instruction": (
                round(float(record.get("seconds", 0.0)) / len(run_seconds), 2)
                if run_seconds else None),
            "separated_entry": separated(entry),
            "cause": cause(frame, float(record.get("seconds", 0.0)),
                           run_seconds)}


def report(records: list[dict]) -> list[str]:
    slow = [r for r in records
            if r.get("population") == "iris"
            and (r["outcome"] == "timeout"
                 or float(r.get("seconds", 0.0)) >= SLOW_SECONDS)]
    rows = [measure(record) for record in slow]
    lines = [f"expensive probes {len(rows)}: "
             + " ".join(f"{name} {count}" for name, count in
                        collections.Counter(r["outcome"] for r in rows).most_common())]
    if not rows:
        return lines
    lines.append("cause: " + " ".join(
        f"{name} {count}" for name, count in
        collections.Counter(r["cause"] for r in rows).most_common()))
    for field in ("conjuncts", "mapsto", "instructions",
                  "seconds_per_instruction"):
        values = sorted(r[field] for r in rows if r[field] is not None)
        if not values:
            lines.append(f"{field}: not measured")
            continue
        lines.append(f"{field}: median {statistics.median(values):.1f} "
                     f"p90 {values[int(0.9 * len(values))]:.1f} "
                     f"max {values[-1]:.1f}")
    worst = collections.Counter()
    for row in rows:
        worst[row["module"]] += 1
    lines.append("ten worst modules (expensive probes each):")
    for name, count in worst.most_common(10):
        sample = next(r for r in rows if r["module"] == name)
        lines.append(f"  {count:3d}  {name:<56s} conjuncts {sample['conjuncts']:3d}"
                     f"  cause {sample['cause']}")
    return lines


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--corpus", type=Path, default=corpus.CORPUS)
    parser.add_argument("--json", type=Path, default=None)
    arguments = parser.parse_args()
    records = corpus.read(arguments.corpus)
    if arguments.json:
        slow = [measure(r) for r in records
                if r.get("population") == "iris"
                and (r["outcome"] == "timeout"
                     or float(r.get("seconds", 0.0)) >= SLOW_SECONDS)]
        arguments.json.write_text(
            "\n".join(json.dumps(row) for row in slow) + "\n")
    for line in report(records):
        print(line)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
