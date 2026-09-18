#!/usr/bin/env python3
"""Print the corpus statistics of section 6 of the residual corpus plan."""

from __future__ import annotations

import argparse
import collections
import statistics
import subprocess
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

import corpus  # noqa: E402

OUTCOMES = ["closed", "residual", "timeout", "error"]
LABELS = ["L1", "L2", "L3", "L4", "L5", "L6", "L7", "L8", "Lother"]
PREDICTIONS = ["C1", "C2", "C3", "C4", "C6", "C7", "C8",
               "unknown", "n/a"]
# Section 9 merged the old class C5, payload, into class C2, memory.
LABEL_TO_CLASS = {"L1": "C1", "L2": "C2", "L3": "C3", "L4": "C4",
                  "L5": "C2", "L6": "C6", "L7": "C7", "L8": "C8"}


def percent(part: int, whole: int) -> str:
    return f"{100.0 * part / whole:.1f}%" if whole else "n/a"


def quantiles(values: list[float]) -> tuple[float, float]:
    if not values:
        return 0.0, 0.0
    ordered = sorted(values)
    index = min(len(ordered) - 1, int(0.9 * len(ordered)))
    return statistics.median(ordered), ordered[index]


def distribution(records: list[dict], field: str, order: list[str]) -> str:
    counts = collections.Counter(record.get(field, "n/a") for record in records)
    known = " ".join(f"{name} {counts.get(name, 0)}" for name in order
                     if counts.get(name, 0))
    extra = " ".join(f"{name} {count}" for name, count in counts.items()
                     if name not in order)
    return " ".join(part for part in (known, extra) if part)


def confusion(records: list[dict]) -> list[str]:
    rows = []
    header = "label".ljust(8) + "".join(name.rjust(9) for name in PREDICTIONS)
    rows.append(header)
    for label in LABELS:
        selected = [r for r in records if r.get("label_class") == label]
        counts = collections.Counter(r.get("pred_class", "n/a") for r in selected)
        rows.append(label.ljust(8) + "".join(
            str(counts.get(name, 0)).rjust(9) for name in PREDICTIONS))
    return rows


def classified(records: list[dict]) -> list[dict]:
    """The records that carry a captured goal, so a prediction exists."""
    return [r for r in records if r.get("pred_class") not in (None, "n/a")]


def agreement(records: list[dict]) -> tuple[int, int, int]:
    """First-goal hits, any-goal hits, and the size of the labeled subset."""
    labeled = [r for r in classified(records)
               if r.get("label_class") in LABEL_TO_CLASS]
    first = sum(1 for r in labeled
                if r["pred_class"] == LABEL_TO_CLASS[r["label_class"]])
    anywhere = sum(1 for r in labeled
                   if LABEL_TO_CLASS[r["label_class"]]
                   in (r.get("pred_detail") or {}).get("classes",
                                                       [r["pred_class"]]))
    return first, anywhere, len(labeled)


def agreement_within_classes(records: list[dict]) -> tuple[int, int]:
    """Agreement counting only records the classifier placed in a class.

    A label can never match a residual goal whose class C1 to C5 does not
    cover, so this figure separates a wrong class from a missing class.
    """
    labeled = [r for r in classified(records)
               if r.get("label_class") in LABEL_TO_CLASS
               and r["pred_class"] != "unknown"]
    hits = sum(1 for r in labeled
               if r["pred_class"] == LABEL_TO_CLASS[r["label_class"]])
    return hits, len(labeled)


def unknown_shapes(records: list[dict]) -> str:
    counts = collections.Counter(
        (r.get("pred_detail") or {}).get("shape", "other")
        for r in records if r.get("pred_class") == "unknown")
    return " ".join(f"{name} {count}" for name, count in counts.most_common())


def error_kinds(records: list[dict]) -> str:
    counts = collections.Counter(r.get("error_kind") or "none"
                                 for r in records
                                 if r.get("outcome") in {"error", "timeout"})
    return " ".join(f"{name} {count}" for name, count in counts.most_common())


def solvers(records: list[dict]) -> str:
    counts = collections.Counter(r.get("solver") or "-" for r in records
                                 if r.get("pred_class") == "C4")
    return " ".join(f"{name} {count}" for name, count in counts.most_common())


def unknown_heads(records: list[dict], limit: int = 10) -> list[tuple[str, int]]:
    heads = collections.Counter()
    for record in records:
        if record.get("pred_class") != "unknown":
            continue
        head = (record.get("pred_detail") or {}).get("head")
        if not head:
            head = (record.get("goal_heads") or ["<none>"])[0]
        heads[head[:70]] += 1
    return heads.most_common(limit)


def disk() -> str:
    output = subprocess.run(["df", "-h", "/home"], capture_output=True,
                            text=True).stdout.strip().split("\n")
    return output[-1] if output else "unknown"


def worktrees() -> int:
    output = subprocess.run(["git", "worktree", "list"], capture_output=True,
                            text=True).stdout
    return len([line for line in output.split("\n") if line.strip()])


def report(records: list[dict], tier: int | None,
           group: str = "iris", modules: set[str] | None = None) -> list[str]:
    if tier is not None:
        records = [r for r in records if r.get("tier") == tier]
    if group != "all":
        records = [r for r in records if r.get("population", "iris") == group]
    if modules:
        records = [r for r in records if r["module"] in modules]
    counts = collections.Counter(r.get("outcome") for r in records)
    ranked = classified(records)
    probed = len(records)
    seconds = [float(r.get("seconds", 0.0)) for r in records]
    median, p90 = quantiles(seconds)
    first, anywhere, labeled = agreement(records)
    within, ranked_labeled = agreement_within_classes(records)
    unknown = sum(1 for r in ranked if r.get("pred_class") == "unknown")
    goals = [r["goal_count"] for r in ranked if r.get("goal_count")]
    not_bi = sum(1 for r in records if r.get("error_kind") == "not_bi")
    lines = [
        f"probed {probed}: " + " ".join(
            f"{name} {counts.get(name, 0)}" for name in OUTCOMES),
        f"closed {percent(counts.get('closed', 0), probed)}; "
        f"error {percent(counts.get('error', 0), probed)} "
        f"of which not_bi {not_bi}; goals captured {len(ranked)}",
        f"error kinds: {error_kinds(records) or 'none'}",
        f"seconds median {median:.1f} p90 {p90:.1f}; goal count median "
        f"{statistics.median(goals) if goals else 0}",
        "pred_class  " + distribution(records, "pred_class", PREDICTIONS),
        "label_class " + distribution(records, "label_class", LABELS),
        f"agreement first goal {first}/{labeled} {percent(first, labeled)}; "
        f"any goal {anywhere}/{labeled} {percent(anywhere, labeled)}; "
        f"within classes {within}/{ranked_labeled} "
        f"{percent(within, ranked_labeled)}",
        f"unknown shapes: {unknown_shapes(records) or 'none'}",
        f"unknown {unknown}/{len(ranked)} {percent(unknown, len(ranked))}; "
        f"C4 solver: {solvers(records) or 'none'}",
        "unknown heads: " + ", ".join(
            f"{head} {count}" for head, count in unknown_heads(records)),
    ]
    lines.extend(confusion(records))
    lines.append(f"disk {disk()}; worktrees {worktrees()}")
    return lines


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--corpus", type=Path, default=corpus.CORPUS)
    parser.add_argument("--tier", type=int, default=None)
    parser.add_argument("--population", default="iris",
                        help="statistics population, or 'all'")
    parser.add_argument("--modules", type=Path, default=None,
                        help="restrict to the modules listed in this file")
    parser.add_argument("--no-confusion", action="store_true")
    arguments = parser.parse_args()
    modules = None
    if arguments.modules:
        modules = {Path(name).name for name in
                   arguments.modules.read_text().split() if name.strip()}
    lines = report(corpus.read(arguments.corpus), arguments.tier,
                   arguments.population, modules)
    for line in lines:
        if arguments.no_confusion and (line.startswith("label")
                                       or line.startswith("L")):
            continue
        print(line)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
