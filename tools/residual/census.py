#!/usr/bin/env python3
"""E3: which statement styles and spec shapes block the automation.

Two questions. What shape does each lemma state, and what shape does each
spec predicate have? Crossing both with the replay says which template the
orchestrator should impose on new modules, and which existing specs are
worth restating.
"""

from __future__ import annotations

import argparse
import collections
import json
import re
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

import corpus  # noqa: E402
from modules import find_proof, parse_module  # noqa: E402
from performance import conjuncts, entry_predicate, statement  # noqa: E402
from replay_report import read as read_replay  # noqa: E402
from signals import opaque_names  # noqa: E402

PROOF_DIR = Path("ZesuSsz/Proofs/WriteSuccess")
WIDE = 12
DEFINITION = re.compile(
    r"(?m)^\s*(?:Global\s+|Local\s+)?Definition\s+(?P<name>[A-Za-z_][\w']*)")
LITHIUM_UNFOLD = re.compile(
    r"LithiumUnfold\s*\(?\s*@?(?P<name>[A-Za-z_][\w']*)")
BARE_MATCH = re.compile(r"\bmatch\b")


def style(text: str) -> str:
    """The statement style of a lemma."""
    if "instr_body" not in text:
        return "no instr_body"
    before = text.split("instr_body", 1)[0]
    if "instr_pre" in before and "□" not in before:
        return "instr_pre adapter"
    if "-∗" in before:
        return "wand into instr_body"
    return "instr_body with the precondition inside"


def spec_shapes(root: Path = PROOF_DIR) -> dict[str, dict]:
    """Every spec predicate of the proof tree, with the four census facts.

    A `LithiumUnfold` instance is anonymous and names its predicate as an
    argument: `Global Instance : LithiumUnfold (@name) := I.`
    """
    sealed = opaque_names()
    unfolds: set[str] = set()
    bodies: dict[str, str] = {}
    for source in sorted(root.glob("*.v")):
        text = source.read_text()
        unfolds.update(found.group("name")
                       for found in LITHIUM_UNFOLD.finditer(text))
        for found in DEFINITION.finditer(text):
            start = found.end()
            end = text.find("\n\n", start)
            bodies[found.group("name")] = text[start:end if end > 0 else len(text)]
    return {name: {"lithium_unfold": name in unfolds,
                   "opaque": name in sealed,
                   "bare_match": bool(BARE_MATCH.search(body)),
                   "conjuncts": conjuncts(body),
                   "wide": conjuncts(body) > WIDE}
            for name, body in bodies.items()}


def lemma_rows(records: list[dict], replays: dict) -> list[dict]:
    rows = []
    for record in records:
        if record.get("population") != "iris":
            continue
        module = PROOF_DIR / record["module"]
        try:
            text = statement(module, record["lemma"])
        except Exception:
            continue
        entry = entry_predicate(text)
        replay = replays.get((record["module"], record["lemma"]))
        rows.append({"module": record["module"], "lemma": record["lemma"],
                     "style": style(text),
                     "entry_conjuncts": conjuncts(entry),
                     "closes_at": replay["closes_at"] if replay else None,
                     "replayed": bool(replay
                                      and replay["outcome"] == "replayed")})
    return rows


def report(rows: list[dict], shapes: dict[str, dict]) -> list[str]:
    lines = [f"lemmas censused {len(rows)}"]
    styles = collections.Counter(row["style"] for row in rows)
    lines.append("statement style: " + " ".join(
        f"{name} {count}" for name, count in styles.most_common()))
    lines.append("style vs closes_at (replayed lemmas only):")
    for name, _ in styles.most_common():
        group = [r for r in rows if r["style"] == name and r["replayed"]]
        if not group:
            continue
        zero = sum(1 for r in group if r["closes_at"] == 0)
        never = sum(1 for r in group if r["closes_at"] is None)
        lines.append(f"  {name:<40s} n {len(group):4d} "
                     f"closes_at 0 {zero:3d}  never {never:3d}")
    wide = [r for r in rows if r["entry_conjuncts"] > WIDE]
    lines.append(f"entry predicates above {WIDE} conjuncts: {len(wide)}")
    lines.append(f"spec predicates {len(shapes)}: "
                 f"LithiumUnfold {sum(1 for s in shapes.values() if s['lithium_unfold'])}"
                 f", Opaque {sum(1 for s in shapes.values() if s['opaque'])}"
                 f", bare match {sum(1 for s in shapes.values() if s['bare_match'])}"
                 f", above {WIDE} conjuncts "
                 f"{sum(1 for s in shapes.values() if s['wide'])}")
    return lines


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--corpus", type=Path, default=corpus.CORPUS)
    parser.add_argument("--replay", type=Path,
                        default=Path("ZesuSsz/Evidence/residuals/replay.jsonl"))
    parser.add_argument("--json", type=Path, default=None)
    arguments = parser.parse_args()
    replays = {(r["module"], r["lemma"]): r for r in read_replay(arguments.replay)}
    rows = lemma_rows(corpus.read(arguments.corpus), replays)
    shapes = spec_shapes()
    if arguments.json:
        arguments.json.write_text(json.dumps({"lemmas": rows, "specs": shapes}))
    for line in report(rows, shapes):
        print(line)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
