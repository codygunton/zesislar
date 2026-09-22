#!/usr/bin/env python3
"""Sort a residual goal into a residual class from its structure.

The classifier reads the captured goal text and nothing else. It never sees
the hand lines that `label.py` reads, so the agreement between the two is a
real measurement and not a restatement of one rule set.

Classes follow the table of section 9, which replaces the classes of
compliance plan 7.6.1:

  C1 trace witness, C2 memory (the old C2 and C5 merged), C3 sealed unfold,
  C4 pure arithmetic, C6 folded hypothesis, C7 code bundle, C8 bare match.

Iteration 1 keyed on the head of the conclusion alone and left 46 percent
unknown. The cause of a residual usually sits in the context, so the rules
below read the context first: a frame handoff over a context that still
holds a folded predicate is C6, and an instruction lookup over a folded code
bundle is C7, whatever their conclusions look like.

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
from population import population  # noqa: E402
from signals import opaque_names, unfold_lemmas  # noqa: E402


IRIS_MARK = re.compile(r"-∗|↦|WPasm|instr_body|instr_pre|⌜|∗|={⊤}=∗|□")
EXISTENTIAL = re.compile(r"^\s*(?:∃|exists)\s+(?P<binder>[^,]{0,200}),")
HYPOTHESIS = re.compile(r'^\s*(?:_|"[^"]*")\s*:\s*(?P<body>.*)$')

# C1 trace: a witness for the block's trace or its events.
TRACE_BINDER = re.compile(r"\bspec\b|isla_trace|\btrace\b")
TRACE_EVIDENCE = re.compile(r"\bscons\b|scons_snap|spec_trace|[Ee]vents?\b")
TRACE_HEAD = re.compile(r"^(spec_trace|writeOutputEvents\w*|\w*Events)$")

# C2 memory: a byte or word of an array, and the payload arrays of the old C5.
MEMORY_FINDS = {"FindMemMapsTo", "FindMemMapsto"}
PREDICATE_FINDS = {"FindDirect", "FindPred", "FindInContext"}
WORD_MAPSTO = re.compile(r"↦ₘ(?![∗*?])|\bmem_mapsto\b")
ARRAY_MAPSTO = re.compile(r"↦ₘ∗|↦ₘ\*|mem_mapsto_array|\barray_at\b")
SLICE_TERM = re.compile(r"\btake\b|\bdrop\b")
SUBSUME_ARRAY = re.compile(r"^subsume\b.{0,400}?↦ₘ∗", re.S)
BYTE_LIST = re.compile(r"list \(bv 8\)")
PAYLOAD_HEAD = re.compile(r"[Pp]ayload|Bytes$|\w*ByteList\w*")
PAYLOAD_TERM = re.compile(r"writeSuccessPayload|_payload_at|_payload|payloadAt"
                          r"|\bpayload\b|list \(bv 8\)|\bbv 8\b|byteList"
                          r"|_bytes\b|\bbytes\b|Bytes\b")

# C3 sealed: a `Global Opaque` name or a closed-contract return predicate.
SEALED_SHAPE = re.compile(r"(Bundle|CallerFrame|Frame|Held|Package|Untouched"
                          r"|Resources|Entry|Post|Block|Return|Exit)$")
SEALED_EQUIV = re.compile(r"^uPred_equiv'\s*\(\s*(?P<name>[\w.']+)")

# C4 pure: arithmetic with no `envs_entails` above it.
PURE_ARITH = re.compile(r"\bbv_\w+|\bbv\s+\d+\b|\bBV\s+\d+\b|%Z\b|%nat\b"
                        r"|\bZ\.\w+|\bN\.\w+|2\s*\^|≪|≫|little_endian_to_bv")
PURE_CONCLUSION = re.compile(r"-∗|↦|WPasm|instr_body|instr_pre|={⊤}=∗|□|∗")
LIST_TERM = re.compile(r"\btake\b|\bdrop\b|\bconcat\b|\+\+|\blist\b|::"
                       r"|\bapp\b|\brev\b|\bmap\b|\bfilter\b")

# C6 folded hypothesis: a frame handoff over a context that is not atomized.
REGISTER_HEAD = re.compile(r'^(reg_col|"x\d+"|"PC"|"pc")$')
FRAME_TERM = re.compile(r"\breg_col\b|↦ᵣ|\binstr_pre\b|\bmmio_range\b")
PROJECT_PREDICATE = re.compile(r"^[A-Za-z][A-Za-z0-9_']{7,}$")
CAMEL = re.compile(r"[a-z][A-Z]")
PRIMITIVE = {"reg_col", "instr", "instr_pre", "instr_body", "mmio_range",
             "spec_trace", "emp", "True", "False", "bi_emp_valid",
             "find_in_context", "subsume", "uPred_equiv'", "big_opL",
             "instr_lookup_resources"}

# C7 code bundle: the instruction lookup blocked by a folded code list.
CODE_BUNDLE = re.compile(r"writeSuccessCompleteNativeCode|spec_instr_resources"
                         r"|instr_lookup_resources|\w*NativeCode\b|\w*CodeList\b")

# C8 bare match: a case split on a spec field, left to the proof.
CASE_SPLIT = re.compile(r"^match\b")

OPENERS = "([{⌜⎡"
CLOSERS = ")]}⌝⎤"
CLASSES = ["C1", "C2", "C3", "C4", "C6", "C7", "C8"]


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


def outside_brackets(text: str, token: str) -> bool:
    """`token` appears in `text` outside every bracket."""
    depth = 0
    for index, character in enumerate(text):
        if character in OPENERS:
            depth += 1
        elif character in CLOSERS:
            depth = max(0, depth - 1)
        elif depth == 0 and text.startswith(token, index):
            return True
    return False


def separated(text: str) -> bool:
    """The text holds a separating conjunction outside every bracket.

    The array arrow `↦ₘ∗` ends in the same star, so its own star never
    counts as a conjunction.
    """
    depth = 0
    index = 0
    while index < len(text):
        character = text[index]
        if text.startswith("↦ₘ∗", index):
            index += 3
            continue
        if character in OPENERS:
            depth += 1
        elif character in CLOSERS:
            depth = max(0, depth - 1)
        elif character == "∗" and depth == 0:
            return True
        index += 1
    return False


def find_kind(goal: str) -> str | None:
    found = re.search(r"find_in_context\s*\(\s*(?P<kind>Find\w+)", goal)
    return found.group("kind") if found else None


def existential_binder(goal: str) -> str | None:
    found = EXISTENTIAL.match(goal.strip())
    return found.group("binder") if found else None


def hypotheses(context: str) -> list[str]:
    """The body of each Iris hypothesis line of the context."""
    bodies = []
    for line in context.split("\n"):
        found = HYPOTHESIS.match(line)
        if found and found.group("body").strip():
            bodies.append(found.group("body").strip())
    return bodies


def folded_names(context: str) -> list[str]:
    """Context hypotheses whose head is a project predicate, still folded.

    Lithium cannot see inside a named project predicate. While one sits in
    the context the automation has nothing to take apart, which is what
    class C6 and class C7 both describe.
    """
    names = []
    for body in hypotheses(context):
        head = head_constant(body)
        if head in PRIMITIVE or not PROJECT_PREDICATE.match(head):
            continue
        if head in opaque_names() or CAMEL.search(head):
            names.append(head)
    return names


def sealed_name(head: str, goal: str, context: str) -> str | None:
    """The sealed constant the goal asks to unfold, if there is one."""
    equivalence = SEALED_EQUIV.match(goal.strip())
    if equivalence:
        name = equivalence.group("name")
        if name in opaque_names() or SEALED_SHAPE.search(name):
            return name
    if head in opaque_names() or head == "encoderIntExactReturn":
        return head
    if not separated(goal) and SEALED_SHAPE.search(head):
        return head
    held = [name for name in folded_names(context) if name in opaque_names()]
    if len(held) == 1 and not separated(goal):
        return held[0]
    return None


def unfold_lemma(name: str) -> str | None:
    candidate = f"{name}_unfold"
    return candidate if candidate in unfold_lemmas() else None


def wants_memory(goal: str, kind: str | None, binder: str | None) -> bool:
    """The goal asks for memory: an array, a slice of one, or a word in one."""
    if kind in MEMORY_FINDS:
        return True
    if SUBSUME_ARRAY.match(goal.strip()):
        return True
    if binder and ARRAY_MAPSTO.search(goal) and SLICE_TERM.search(goal):
        return True
    # The goal IS an array, rather than merely mentioning one.
    if outside_brackets(goal, "↦ₘ∗") and not separated(goal):
        return True
    if kind in PREDICATE_FINDS and WORD_MAPSTO.search(goal):
        return True
    return bool(WORD_MAPSTO.search(head_constant(goal))) and not separated(goal)


def frame_handoff(goal: str) -> bool:
    """The conclusion hands a bundle of resources on, rather than asking one."""
    head = head_constant(goal)
    if REGISTER_HEAD.match(head):
        return True
    return separated(goal) and bool(FRAME_TERM.search(goal))


def classify_goal(block: str) -> Prediction:
    """The class of one printed goal, context first."""
    context, goal = split_goal(block)
    head = head_constant(goal)
    kind = find_kind(goal)
    binder = existential_binder(goal)
    folded = folded_names(context)
    detail: dict = {"head": head}
    if kind:
        detail["find"] = kind
    if binder:
        detail["head"] = f"∃ {' '.join(binder.split())[:40]}"
    if folded:
        detail["folded"] = folded[:4]

    if kind == "FindInstrKind":
        detail["bundle"] = bool(CODE_BUNDLE.search(context))
        return Prediction("C7", detail)

    if CASE_SPLIT.match(goal.strip()):
        return Prediction("C8", detail)

    if binder and TRACE_BINDER.search(binder) and TRACE_EVIDENCE.search(goal):
        return Prediction("C1", detail)
    if TRACE_HEAD.match(head) or (kind in PREDICATE_FINDS
                                  and TRACE_EVIDENCE.search(goal)
                                  and not WORD_MAPSTO.search(goal)):
        return Prediction("C1", detail)

    if wants_memory(goal, kind, binder):
        detail["arrays"] = [line.strip()[:120] for line in context.split("\n")
                            if ARRAY_MAPSTO.search(line)][:4]
        return Prediction("C2", detail)
    if binder and BYTE_LIST.search(binder):
        return Prediction("C2", detail)

    if frame_handoff(goal) and folded:
        return Prediction("C6", detail)

    sealed = sealed_name(head, goal, context)
    if sealed:
        detail.update({"sealed": sealed, "unfold": unfold_lemma(sealed)})
        return Prediction("C3", detail)

    pure = not PURE_CONCLUSION.search(goal)
    if pure and PURE_ARITH.search(goal) and not LIST_TERM.search(goal):
        return Prediction("C4", detail)
    if pure and PAYLOAD_TERM.search(goal):
        return Prediction("C2", detail)
    if PAYLOAD_HEAD.search(head) and not separated(goal):
        return Prediction("C2", detail)

    if frame_handoff(goal):
        detail["shape"] = "frame handoff, context already atomized"
    elif separated(goal):
        detail["shape"] = "separating conjunction"
    elif binder:
        detail["shape"] = "uninferable existential"
    return Prediction("unknown", detail)


def full_goal_text(record: dict, goal_dir: Path | None) -> str:
    """The complete goal text when it was kept, else the 8 KiB head."""
    digest = record.get("goal_sha256")
    if goal_dir and digest:
        stored = Path(goal_dir) / f"{digest}.txt"
        if stored.exists():
            return stored.read_text()
    return record.get("goal_text", "")


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
    parser.add_argument("--goal-dir", type=Path, default=None,
                        help="directory of full goal texts, named by hash")
    arguments = parser.parse_args()
    source = arguments.record.read_text() if arguments.record else sys.stdin.read()
    for line in source.split("\n"):
        if not line.strip():
            continue
        record = json.loads(line)
        goal_text = full_goal_text(record, arguments.goal_dir)
        prediction = classify(goal_text, "residual" if goal_text
                              else record.get("outcome", "residual"))
        record["pred_class"] = prediction.pred_class
        record["pred_detail"] = prediction.detail
        record["population"] = population(
            record["module"], record["lemma"],
            record.get("label_lines", []), record.get("error_kind", ""))
        print(json.dumps(record))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
