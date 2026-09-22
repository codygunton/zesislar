#!/usr/bin/env python3
"""Rank the automation opportunities the replay found.

One row per gap pattern: the class of the goal at which the block
automation stopped, and the normalized signature of that goal. Ranked by
hand lines saved.

Iteration 2 keyed rows on (class, first word of the tactic). No rule author
can act on "C1 with iIntros", so iteration 3 keys on the goal shape and
carries a sample conclusion and the exact sentences that closed it.

The remedy column is a proposal. This plan never patches an automation
file; the compliance orchestrator owns every such change.
"""

from __future__ import annotations

import argparse
import collections
import sys
from dataclasses import dataclass, field
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

from replay_report import goal_shape, read, replayed  # noqa: E402
from tiers import rule_15_modules  # noqa: E402

OUTPUT = Path("ZesuSsz/Evidence/residuals/AUTOMATION_BACKLOG.md")
MIN_PROOFS = 3
SAMPLE_LINES = 5
RESUME_SENTENCES = 6
# Section 12 item 4: the instruction fetch and its `find_in_context` are one
# gap. Both stop because the code resources sit folded in the context.
MERGED = "code resources folded"
CODE_SIGNATURES = ("find_in_context(FindInstrKind)", "∃ : option isla_trace")

REMEDY = {
    "C1": ("Compute the events term in the postcondition and close the trace"
           " side condition inside `zesu_finish`.", "auto", "half day"),
    "C2": ("Add array slice subsumption and word-in-array rules.",
           "auto", "day"),
    "C3": ("Apply the `_unfold` lemma, or register a `LithiumUnfold`"
           " instance, at the closed-contract exit.", "auto", "half day"),
    "C4": ("Add the closing shapes to the finisher.", "auto", "hour"),
    "C6": ("State the precondition inside `instr_body`, and give the named"
           " predicate a `LithiumUnfold` instance.", "orchestrator",
           "half day"),
    "C7": ("Register the code bundle names in `zesu_expose_code_lists`.",
           "auto", "hour"),
    "C8": ("Give the spec a known shape, or add a `case_destruct` hook.",
           "orchestrator", "half day"),
    "error": ("The automation raises or exceeds its budget here. Diagnose"
              " first: a raising tactic hides every gap behind it.",
              "auto", "half day"),
    "unknown": ("No class covers this shape yet. Read the sample below"
                " before proposing a rule.", "lead", "unknown"),
    MERGED: ("Register the code bundle names in `zesu_expose_code_lists` so"
             " the instruction fetch sees the code resources, instead of"
             " leaving `instr_lookup_resources`, `spec_instr_resources` and"
             " `writeSuccessCompleteNativeCode` folded in the context.",
             "auto", "hour"),
    "closed": ("The automation already finishes here; the line is dead"
               " weight.", "orchestrator", "hour"),
}
SKIP_SHAPES = {"unseen"}


@dataclass
class Gap:
    shape: str
    signature: str
    lines: int = 0
    proofs: set = field(default_factory=set)
    recent_lines: int = 0
    recent_proofs: set = field(default_factory=set)
    sample: str = ""
    sentences: list = field(default_factory=list)
    tactics: collections.Counter = field(default_factory=collections.Counter)


def merge_signature(shape: str, text: str) -> tuple[str, str]:
    """Fold the two instruction-fetch shapes into one gap."""
    if any(text.startswith(mark) for mark in CODE_SIGNATURES):
        return MERGED, MERGED
    return shape, text


def resume_sentences(steps: dict, start: int, closes_at: int | None) -> list[str]:
    """Every sentence from the stop to the first step the automation closed.

    The author's next sentence alone does not say what unblocked the
    automation; the block up to the resume point does.
    """
    last = closes_at if closes_at is not None else max(steps, default=start)
    text = []
    for index in range(start, min(last, start + RESUME_SENTENCES - 1) + 1):
        sentence = (steps.get(index) or {}).get("sentence")
        if sentence:
            text.append(sentence)
    return text


def gaps(records: list[dict]) -> list[Gap]:
    """One entry per (class, conclusion signature) the hand lines answered."""
    recent = {Path(name).name for name in rule_15_modules(Path("."))}
    found: dict[tuple[str, str], Gap] = {}
    for record in replayed(records):
        steps = {step["index"]: step for step in record["steps"]}
        last = record["closes_at"]
        if last is None:
            last = max(steps) if steps else 0
        for index in range(1, last + 1):
            before, line = steps.get(index - 1), steps.get(index)
            if line is None:
                continue
            shape = goal_shape(before)
            if shape in SKIP_SHAPES:
                continue
            marks = (before or {}).get("signatures") or ["(no goal)"]
            shape, mark = merge_signature(shape, marks[0])
            key = (shape, mark)
            gap = found.setdefault(key, Gap(shape, mark))
            gap.lines += 1
            gap.proofs.add((record["module"], record["lemma"]))
            gap.tactics[line.get("tactic", "?")] += 1
            if record["module"] in recent:
                gap.recent_lines += 1
                gap.recent_proofs.add((record["module"], record["lemma"]))
            if not gap.sentences:
                gap.sentences = resume_sentences(steps, index,
                                                 record["closes_at"])
            if not gap.sample and (before or {}).get("samples"):
                gap.sample = before["samples"][0]
    return sorted(found.values(), key=lambda gap: -gap.lines)


def row(rank: int, gap: Gap) -> str:
    _, owner, size = REMEDY.get(gap.shape, REMEDY["unknown"])
    return (f"| {rank} | {gap.shape} | `{gap.signature}` | {len(gap.proofs)} "
            f"| {gap.lines} | {len(gap.recent_proofs)} | {gap.recent_lines} "
            f"| {size} | {owner} |")


def detail(gap: Gap) -> list[str]:
    remedy = REMEDY.get(gap.shape, REMEDY["unknown"])[0]
    tactics = ", ".join(f"`{name}` {count}"
                        for name, count in gap.tactics.most_common(4))
    text = [f"### {gap.shape} — `{gap.signature}`", "",
            f"{len(gap.proofs)} proofs, {gap.lines} hand lines. "
            f"Tactics used: {tactics}.", "",
            "Sample conclusion:", "", "```"]
    text += gap.sample.split("\n")[:SAMPLE_LINES]
    text += ["```", "",
             "Sentences from the stop to the first step the automation"
             " closed:", "", "```"]
    text += (gap.sentences or ["(not recorded)"])
    text += ["```", "", f"Proposed rule: {remedy}", ""]
    return text


def document(records: list[dict], title: str, limit: int) -> str:
    ranked = gaps(records)
    main = [gap for gap in ranked if len(gap.proofs) >= MIN_PROOFS]
    rare = [gap for gap in ranked if len(gap.proofs) < MIN_PROOFS]
    done = replayed(records)
    early = [r for r in done if r["closes_at"] is not None]
    saved = sum(max(0, r["n_sentences"] - 1 - r["closes_at"]) for r in early)
    text = [f"# Automation backlog ({title})", "",
            "Generated by `tools/residual/backlog.py` from the E1 replay of",
            "`PLAN_RESIDUAL_CORPUS.md` section 10, reclassified per section",
            "11. One row per gap pattern: the class of the goal at which the",
            "block automation stopped, and the normalized signature of that",
            "goal. Ranked by hand lines saved.", "",
            "This file proposes rules. It never patches one.", "",
            f"Replays read: {len(records)}, of which {len(done)} completed.",
            f"Proofs the automation already finishes before their last line:",
            f"{len(early)} of {len(done)}, leaving {saved} sentences that are",
            f"dead weight today. Needed hand lines: "
            f"{sum(gap.lines for gap in ranked)} over {len(ranked)} patterns,",
            f"{len(main)} of them in three proofs or more.", "",
            "Ranked by hand lines over the whole replayed population. The"
            " rule-15-era columns count the same rows inside the modules"
            " written after the rule-15 automation landed, which is the"
            " population the harness must serve; a second table ranks by"
            " those.", "",
            "| rank | class | conclusion signature | proofs | lines |"
            " r15 proofs | r15 lines | size | owner |",
            "| --- | --- | --- | --- | --- | --- | --- | --- | --- |"]
    for rank, gap in enumerate(main[:limit], start=1):
        text.append(row(rank, gap))
    recent = sorted((gap for gap in main if gap.recent_lines),
                    key=lambda gap: -gap.recent_lines)
    text += ["", "## Ranked by rule-15-era hand lines", "",
             "| rank | class | conclusion signature | r15 proofs | r15 lines |"
             " all lines |", "| --- | --- | --- | --- | --- | --- |"]
    for rank, gap in enumerate(recent[:limit], start=1):
        text.append(f"| {rank} | {gap.shape} | `{gap.signature}` | "
                    f"{len(gap.recent_proofs)} | {gap.recent_lines} | "
                    f"{gap.lines} |")
    text += ["", "## The rows in detail", ""]
    for gap in main[:limit]:
        text += detail(gap)
    text += ["## Appendix: patterns in fewer than three proofs", "",
             "| class | conclusion signature | proofs | lines |",
             "| --- | --- | --- | --- |"]
    for gap in rare[:120]:
        text.append(f"| {gap.shape} | `{gap.signature}` | "
                    f"{len(gap.proofs)} | {gap.lines} |")
    return "\n".join(text) + "\n"


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--replay", type=Path,
                        default=Path("ZesuSsz/Evidence/residuals/replay.jsonl"))
    parser.add_argument("--output", type=Path, default=OUTPUT)
    parser.add_argument("--title", default="v3")
    parser.add_argument("--limit", type=int, default=20)
    arguments = parser.parse_args()
    records = read(arguments.replay)
    arguments.output.write_text(document(records, arguments.title,
                                         arguments.limit))
    print(f"{arguments.output}: {len(gaps(records))} patterns")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
