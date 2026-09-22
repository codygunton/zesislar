#!/usr/bin/env python3
"""Label a proof from its hand lines.

The label says which residual class the author of the proof actually closed
by hand. It reads the original proof body only; it never reads the goal that
the probe captured. `classify.py` reads the goal and never the hand lines, so
the two stay independent and the agreement figure means something.

The templates follow the class table of section 9. Class L5 is gone: the old
payload class merged into L2, as class C5 merged into C2.
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

# L1 trace: the author supplied the trace or events witness by hand.
TRACE_WITNESS = re.compile(
    r"iExists.{0,300}?[Ee]vents|\bspec_trace\b|\bscons\b|\bscons_snap\b"
    r"|\bspec_subseteq\b|iExists.{0,200}?\bspec\b", re.S)

# L2 memory: the author split, recombined or located an array by hand. The
# payload idioms of the old L5 belong here too.
MEMORY_STEP = re.compile(
    r"find_in_context_mem_mapsto_semantic|\bMKArray\b|mem_mapsto_array\w*"
    r"|\barray_at\b|_array_byte_value\b|array_byte_\w+|\bbyte_array_at\b"
    r"|\btake_take\b|\bdrop_drop\b|\btake_drop\b|\bapp_length\b"
    r"|_payload_at|_payload|writeSuccessPayload|\bHnative\b"
    r"|\bliInst\b.{0,120}?\b(index|offset|idx|byte|word)\b", re.S)

# L3 sealed: the author unfolded a sealed name by hand.
SEALED_UNFOLD = re.compile(r"\w+_unfold\b|\bencoderIntExactReturn\b", re.S)

# L4 pure: nothing but arithmetic.
PURE_GLUE = re.compile(
    r"^(intros?|move\s*=>.*|clear(\s.*)?|subst(\s.*)?|iStartProof"
    r"|intros?\s+[\w\s]*)$")
PURE_SOLVER = re.compile(
    r"^(all\s*:\s*)?(bv_solve|bv_simplify|bv_simplify_arith|lia|nia"
    r"|reflexivity|done|bv_simplify;\s*lia)$")
PURE_HAVE = re.compile(
    r"^(have|assert)\b.*\bby\s*\(?\s*(bv_solve|bv_simplify;\s*lia|lia"
    r"|reflexivity|done)\s*\)?$", re.S)

# L6 folded hypothesis: the author took a NAMED project predicate apart by
# hand. Plain `iEval (rewrite ...)` is ordinary glue and stays out; what marks
# the class is a camelCase project name inside the step.
FOLDED_STEP = re.compile(
    r"iEval\s*\(\s*(?:unfold|rewrite)\s*/?\s*[a-z]\w*[A-Z]\w{4,}"
    r"|iRename\s+select\s*\(?\s*[a-z]\w*[A-Z]\w{4,}"
    r"|iDestruct\s+select\s*\(\s*[a-z]\w*[A-Z]\w{4,}"
    r"|rewrite\s+/reg_col|\bunfold\s+[a-z]\w*[A-Z]\w{4,}")

# L7 code bundle: the author exposed the code list or the instruction bundle.
CODE_STEP = re.compile(
    r"zesu_expose_code_lists|zesu_reduce_introduced_code_lists"
    r"|instr_lookup_resources|spec_instr_resources|NativeCode\b"
    r"|instr_pre_to_body|\bzesu_open_requested_instr_bundle\b")

# L8 bare match: the author case split on a spec field.
CASE_STEP = re.compile(
    r"\bdestruct\s+\(?\s*\w*(Data|Rows|Items|List|Transactions|Entries)\b"
    r"|\bcase_destruct\b|\bcase:\s|\bdestruct\s+\w+\s+as\s*\[\s*\|")

CLASS_ORDER = ["L1", "L2", "L3", "L4", "L6", "L7", "L8"]


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
    if TRACE_WITNESS.search(text):
        found.append("L1")
    if MEMORY_STEP.search(text):
        found.append("L2")
    if SEALED_UNFOLD.search(text) or opaque_pattern().search(text):
        found.append("L3")
    words = tactic_words(hand_lines)
    if words and all(PURE_GLUE.match(word) or PURE_SOLVER.match(word)
                     or PURE_HAVE.match(word) for word in words):
        found.append("L4")
    if FOLDED_STEP.search(text):
        found.append("L6")
    if CODE_STEP.search(text):
        found.append("L7")
    if CASE_STEP.search(text):
        found.append("L8")
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
