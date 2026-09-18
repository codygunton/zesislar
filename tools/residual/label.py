#!/usr/bin/env python3
"""Label a proof from its hand lines.

The label says which residual class the author of the proof actually closed
by hand. It reads the original proof body only; it never reads the goal that
the probe captured. `classify.py` reads the goal and never the hand lines, so
the two stay independent and the agreement figure means something.
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

from modules import parse_module  # noqa: E402
from signals import opaque_pattern  # noqa: E402

EVENTS_WITNESS = re.compile(r"iExists.{0,300}?[Ee]vents", re.S)
TRACE_WITNESS = re.compile(r"\bspec_trace\b|\bscons\b|\bspec_subseteq\b")
ARRAY_CONTEXT = re.compile(
    r"find_in_context_mem_mapsto_semantic|\bMKArray\b"
    r"|\bliInst\b.{0,120}?\b(index|offset|idx|byte|word)\b"
    r"|mem_mapsto_array\w*|\barray_at\b|_array_byte_value\b"
    r"|array_byte_\w+|\bbyte_array_at\b", re.S)
# Section 4.3 keys class L3 on `iEval (rewrite ..._unfold)` and on
# `encoderIntExactReturn`. A bare `iEval (rewrite /x)` is ordinary definitional
# rewriting, so it stays out; `opaque_pattern()` adds the sealed names.
SEALED_UNFOLD = re.compile(
    r"\w+_unfold\b|\bencoderIntExactReturn\b", re.S)
PURE_GLUE = re.compile(
    r"^(intros?|move\s*=>.*|clear(\s.*)?|subst(\s.*)?|iStartProof"
    r"|intros?\s+[\w\s]*)$")
PURE_SOLVER = re.compile(
    r"^(all\s*:\s*)?(bv_solve|bv_simplify|bv_simplify_arith|lia|nia"
    r"|reflexivity|done|bv_simplify;\s*lia)$")
PURE_HAVE = re.compile(
    r"^(have|assert)\b.*\bby\s*\(?\s*(bv_solve|bv_simplify;\s*lia|lia"
    r"|reflexivity|done)\s*\)?$", re.S)
PAYLOAD = re.compile(r"_payload_at|\bHnative\b|writeSuccessPayload|_payload")
CLASS_ORDER = ["L1", "L2", "L3", "L4", "L5"]


def tactic_words(hand_lines: list[str]) -> list[str]:
    """The hand lines split into single tactic calls."""
    words: list[str] = []
    for line in hand_lines:
        for piece in re.split(r"\.(?:\s|$)|;", line.strip()):
            piece = piece.strip().rstrip(".").strip()
            if piece:
                words.append(piece)
    return words


def label_classes(hand_lines: list[str]) -> list[str]:
    """Every class the hand lines carry, in class order."""
    text = "\n".join(hand_lines)
    found: list[str] = []
    if EVENTS_WITNESS.search(text) or TRACE_WITNESS.search(text):
        found.append("L1")
    if ARRAY_CONTEXT.search(text):
        found.append("L2")
    if SEALED_UNFOLD.search(text) or opaque_pattern().search(text):
        found.append("L3")
    words = tactic_words(hand_lines)
    if words and all(PURE_GLUE.match(word) or PURE_SOLVER.match(word)
                     or PURE_HAVE.match(word) for word in words):
        found.append("L4")
    if PAYLOAD.search(text):
        found.append("L5")
    return sorted(found, key=CLASS_ORDER.index) or ["Lother"]


def label_proof(hand_lines: list[str]) -> tuple[str, list[str]]:
    classes = label_classes(hand_lines)
    return classes[0], classes


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("module", type=Path)
    parser.add_argument("lemma", nargs="?")
    arguments = parser.parse_args()
    for proof in parse_module(arguments.module):
        if arguments.lemma and proof.name != arguments.lemma:
            continue
        first, classes = label_proof(proof.hand_lines)
        print(json.dumps({"module": proof.module, "lemma": proof.name,
                          "label_class": first, "label_classes": classes,
                          "label_lines": proof.body}))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
