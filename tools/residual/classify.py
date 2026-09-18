#!/usr/bin/env python3
"""Sort a residual goal into a residual class from its structure.

The classifier reads the captured goal text and nothing else. It never sees
the hand lines that `label.py` reads, so the agreement between the two is a
real measurement and not a restatement of one rule set.

Classes follow section 7.6.1 of the compliance plan:
  C1 events witness, C2 word in array, C3 sealed unfold,
  C4 bitvector arithmetic, C5 payload per site.

Every rule keys on the head of the conclusion, on the Lithium
`find_in_context` kind, or on the shape of the context. A name that merely
appears somewhere inside a large conjunction decides nothing: a goal whose
conclusion is a separating conjunction of resources is a frame handoff, and
this classifier reports it as `unknown` with its head, which is what tells
the lead that the residual classes need another entry.

`pred_class` is the class of the first goal, the one the author of the proof
meets first. `pred_detail["classes"]` keeps the class of every residual goal.
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from dataclasses import dataclass, field
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

from goals import conclusion, head_constant, is_rule, split_goal, split_goals  # noqa: E402
from signals import opaque_names, unfold_lemmas  # noqa: E402

IRIS_MARK = re.compile(r"-∗|↦|WPasm|instr_body|instr_pre|⌜|∗|={⊤}=∗|□")
EXISTENTIAL = re.compile(r"^\s*(?:∃|exists)\s+(?P<binder>[^,]{0,200}),")
EVENT_TERM = re.compile(r"\bspec\b|\bspec_trace\b|[Ee]vents?\b|\btrace\b"
                        r"|writeOutputEvents|\bscons\b|\bSeen\b")
TRACE_HEAD = re.compile(r"^(spec_trace|writeOutputEvents\w*|\w*Events)$")
FIND_KIND = re.compile(r"find_in_context\s*\(\s*(?P<kind>Find\w+)")
MEMORY_FINDS = {"FindMemMapsTo", "FindMemMapsto"}
REGISTER_FINDS = {"FindRegMapsTo", "FindStructRegMapsTo"}
PREDICATE_FINDS = {"FindDirect", "FindPred", "FindInContext"}
WORD_MAPSTO = re.compile(r"↦ₘ(?![∗*?])|\bmem_mapsto\b")
ARRAY_MAPSTO = re.compile(r"↦ₘ∗|↦ₘ\*|mem_mapsto_array|\barray_at\b")
SEALED_SHAPE = re.compile(r"(Bundle|CallerFrame|Frame|Held|Package|Untouched"
                          r"|Resources|Entry|Post|Block)$")
# Class C4 is bitvector and integer arithmetic. A goal that also carries a
# list term is list algebra, not arithmetic, whatever indices it contains.
PURE_ARITH = re.compile(r"\bbv\s+\d+\b|\bbv_unsigned\b|\bbv_signed\b"
                        r"|\bZ_to_bv\b|\bbv_add\b|\bbv_sub\b|\bbv_mul\b"
                        r"|\bBV\s+\d+\b|%Z\b|\bZ\.\w+|2\s*\^|%nat\b"
                        r"|\bN\.\w+")
LIST_TERM = re.compile(r"\btake\b|\bdrop\b|\bconcat\b|\+\+|\blist\b|::"
                       r"|\bapp\b|\brev\b|\bmap\b|\bfilter\b")
PAYLOAD_HEAD = re.compile(r"[Pp]ayload|Bytes$|\w*ByteList\w*")
PAYLOAD_TERM = re.compile(r"writeSuccessPayload|_payload_at|_payload"
                          r"|payloadAt|\bpayload\b|list \(bv 8\)|\bbv 8\b"
                          r"|byteList|_bytes\b|\bbytes\b|Bytes\b")
OPENERS = "([{⌜⎡"
CLOSERS = ")]}⌝⎤"


@dataclass
class Prediction:
    pred_class: str
    detail: dict = field(default_factory=dict)


def iris_goal(block: str) -> bool:
    """The goal is an Iris entailment, the `envs_entails` shape."""
    if any(is_rule(line) and set(line.strip()) - {"="}
           for line in block.split("\n")):
        return True
    return bool(IRIS_MARK.search(split_goal(block)[1]))


def separated(text: str) -> bool:
    """The text holds a separating conjunction outside every bracket."""
    depth = 0
    for character in text:
        if character in OPENERS:
            depth += 1
        elif character in CLOSERS:
            depth = max(0, depth - 1)
        elif character == "∗" and depth == 0:
            return True
    return False


def find_kind(goal: str) -> str | None:
    found = FIND_KIND.search(goal)
    return found.group("kind") if found else None


def existential_binder(goal: str) -> str | None:
    found = EXISTENTIAL.match(goal.strip())
    return found.group("binder") if found else None


def sealed_head(head: str, goal: str) -> str | None:
    """The sealed constant the goal asks to unfold, if it heads the goal."""
    if head in opaque_names():
        return head
    if head == "encoderIntExactReturn":
        return head
    if not separated(goal) and SEALED_SHAPE.search(head):
        return head
    return None


def unfold_lemma(name: str) -> str | None:
    candidate = f"{name}_unfold"
    return candidate if candidate in unfold_lemmas() else None


def array_terms(context: str) -> list[str]:
    return [line.strip()[:160] for line in context.split("\n")
            if ARRAY_MAPSTO.search(line)][:4]


def index_terms(text: str) -> list[str]:
    return re.findall(r"(?:\+\s*BV\s+\d+\s+|\+\s*)(0x[0-9a-fA-F]+|\d+)", text)[:4]


def classify_goal(block: str) -> Prediction:
    """The class of one printed goal."""
    context, goal = split_goal(block)
    head = head_constant(goal)
    kind = find_kind(goal)
    detail: dict = {"head": head}
    if kind:
        detail["find"] = kind

    binder = existential_binder(goal)
    if binder:
        detail["head"] = f"∃ {' '.join(binder.split())[:40]}"
        if EVENT_TERM.search(binder):
            return Prediction("C1", detail)
    if TRACE_HEAD.match(head) and not separated(goal):
        return Prediction("C1", detail)
    wants_word = bool(WORD_MAPSTO.search(goal)) and not ARRAY_MAPSTO.search(goal)
    if kind in PREDICATE_FINDS and not wants_word \
            and EVENT_TERM.search(head + " " + goal[:200]):
        return Prediction("C1", detail)

    if kind in MEMORY_FINDS or (kind in PREDICATE_FINDS and wants_word) \
            or (WORD_MAPSTO.search(head) and not separated(goal)):
        if ARRAY_MAPSTO.search(context):
            detail.update({"arrays": array_terms(context),
                           "indices": index_terms(goal)})
            return Prediction("C2", detail)

    sealed = sealed_head(head, goal)
    if sealed:
        detail.update({"sealed": sealed, "unfold": unfold_lemma(sealed)})
        return Prediction("C3", detail)

    if not iris_goal(block) and PURE_ARITH.search(goal) \
            and not LIST_TERM.search(goal):
        return Prediction("C4", detail)

    if PAYLOAD_HEAD.search(head) or (not separated(goal)
                                     and PAYLOAD_TERM.search(goal)
                                     and not iris_goal(block)):
        return Prediction("C5", detail)

    if separated(goal):
        detail["shape"] = "separating conjunction"
    return Prediction("unknown", detail)


def classify(goal_text: str, outcome: str = "residual") -> Prediction:
    if outcome != "residual" or not goal_text.strip():
        return Prediction("n/a")
    blocks = split_goals(goal_text)
    if not blocks:
        return Prediction("unknown", {"head": ""})
    predictions = [classify_goal(block) for block in blocks]
    first = predictions[0]
    first.detail["classes"] = [p.pred_class for p in predictions]
    first.detail["heads"] = [conclusion(block)[:80] for block in blocks][:8]
    return first


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("record", type=Path, nargs="?",
                        help="a corpus.jsonl file to reclassify on stdout")
    arguments = parser.parse_args()
    source = arguments.record.read_text() if arguments.record else sys.stdin.read()
    for line in source.split("\n"):
        if not line.strip():
            continue
        record = json.loads(line)
        goal_text = record.get("goal_text", "")
        prediction = classify(goal_text, "residual" if goal_text
                              else record.get("outcome", "residual"))
        record["pred_class"] = prediction.pred_class
        record["pred_detail"] = prediction.detail
        print(json.dumps(record))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
