#!/usr/bin/env python3
"""Plan 16 item 1: why only a few benchmark lemmas close.

Inputs are measurements, not probes: the two whole-corpus arms (v1 and
v2), and a replay of every benchmark lemma under v1 and under v2. Every
replay step is reclassified from its stored goal text with the given
classifier, so both replays are read by the same version.

Definitions used below.

- A *stop* is a maximal run of consecutive replay steps where the
  automation does not finish and the first goal has one class. The *stall
  sequence* of a lemma is its list of stops, in proof order. A step where
  the automation raised, or ran past its 30 second step budget, is class
  `raised` (the replay cannot tell the two apart); the steps a timed-out
  replay never reached are one final stop of class `unreplayed`.
- A v2 replay that aborted because a hand sentence failed under v2 (the
  rule set did the sentence's work) keeps its v1 sequence; the count of
  such lemmas is printed.
- A v1 stop is *covered by v2* when, at every step of the run, v2 either
  finishes or stops with a different class.
- A lemma *closes under a rule set R* when every class in its v2 stall
  sequence is in R. This is the model behind the smallest-set figures; it
  assumes one rule per class, which is optimistic for a class that holds
  several shapes (C1, C2, unknown), and it is said so wherever it is used.
- For the whole corpus the benchmark set supplies the sequences. A residual
  outside the set has only its first stop (from the corpus arm), so its
  chance to close under R is the benchmark rate for the same first-stop
  class. Those figures are estimates and are printed as such.
"""

from __future__ import annotations

import argparse
import collections
import importlib
import itertools
import json
import sys
from pathlib import Path

RESTATEMENT = {"C6", "C8"}


def read_jsonl(path: Path) -> list[dict]:
    return [json.loads(line) for line in path.read_text().split("\n") if line]


def last_by_lemma(records: list[dict]) -> dict[tuple[str, str], dict]:
    return {(r["module"], r["lemma"]): r for r in records}


def raised_kind(text: str | None) -> str:
    """Why the automation raised at a step, from the message probe."""
    if text is None:
        return "raised"
    if "tclTIMEOUT" in text or "Timeout" in text:
        return "slow"
    if "not a BI assertion" in text:
        return "raised-pure"
    return "raised-other"


def family(name: str) -> str:
    """The v1 name of a class the message probe split."""
    return "raised" if name in ("raised-pure", "slow", "raised-other") else name


def step_class(step: dict, goals: Path, classify_goal,
               messages: dict | None = None) -> str:
    if step.get("closes") and not step.get("goals"):
        return "closes"
    if step.get("failed"):
        if messages is None:
            return "raised"
        return raised_kind(messages.get(str(step["index"])))
    digests = step.get("goal_sha256") or []
    if not digests:
        return "closes" if step.get("closes") else "raised"
    stored = goals / f"{digests[0]}.txt"
    if not stored.exists():
        return (step.get("classes") or ["unknown"])[0]
    return classify_goal(stored.read_text()).pred_class


def step_classes(record: dict, goals: Path, classify_goal,
                 messages: dict | None = None) -> list[str]:
    classes = [step_class(step, goals, classify_goal, messages)
               for step in record.get("steps", [])]
    reached = record.get("steps_reached") or len(classes)
    if record.get("outcome") == "timeout":
        classes = classes[:reached] + ["unreplayed"]
    elif record.get("outcome") == "error":
        classes = ["error"]
    return classes


def stops(classes: list[str]) -> list[tuple[str, list[int]]]:
    """Maximal runs of one non-finishing class, with their step indices."""
    runs: list[tuple[str, list[int]]] = []
    for index, name in enumerate(classes):
        if name == "closes":
            continue
        if runs and runs[-1][0] == name and runs[-1][1][-1] == index - 1:
            runs[-1][1].append(index)
        else:
            runs.append((name, [index]))
    return runs


def closes_at_start(classes: list[str]) -> bool:
    return bool(classes) and classes[0] == "closes"


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--corpus-v1", type=Path, required=True)
    parser.add_argument("--corpus-v2", type=Path, required=True)
    parser.add_argument("--replay-v1", type=Path, required=True)
    parser.add_argument("--replay-v2", type=Path, required=True)
    parser.add_argument("--goals", type=Path, required=True,
                        help="the directory of stored replay goal texts")
    parser.add_argument("--classifier", type=Path, required=True,
                        help="the directory holding classify.py to use")
    parser.add_argument("--messages-v2", type=Path, default=None,
                        help="the v2 message probe, to split `raised` into "
                             "raised-pure, slow and raised-other")
    parser.add_argument("--out", type=Path, required=True,
                        help="per-lemma stall sequences, JSON lines")
    arguments = parser.parse_args()

    sys.path.insert(0, str(arguments.classifier))
    classify = importlib.import_module("classify")
    version = getattr(classify, "VERSION", "1")

    corpus = {}
    for name, path in (("v1", arguments.corpus_v1), ("v2", arguments.corpus_v2)):
        corpus[name] = json.loads(path.read_text())["rows"]
    total = len(corpus["v1"])
    print(f"classifier v{version}; corpus {total} lemmas")
    for name, rows in corpus.items():
        outcomes = collections.Counter(row["outcome"] for row in rows)
        closed = outcomes.get("closed", 0)
        print(f"(a) {name}: closed {closed} of {total} "
              f"({100 * closed / total:.1f} %); {dict(sorted(outcomes.items()))}")

    replays = {"v1": last_by_lemma(read_jsonl(arguments.replay_v1)),
               "v2": last_by_lemma(read_jsonl(arguments.replay_v2))}
    lemmas = sorted(set(replays["v1"]) & set(replays["v2"]))
    messages = ({key: record.get("messages") or {} for key, record in
                 last_by_lemma(read_jsonl(arguments.messages_v2)).items()}
                if arguments.messages_v2 else {})
    print(f"(b) replayed under both: {len(lemmas)} benchmark lemmas")

    sequences = {}
    fallback = 0
    covered = total_stops = 0
    by_class_total = collections.Counter()
    by_class_covered = collections.Counter()
    with arguments.out.open("w") as handle:
        for key in lemmas:
            one = step_classes(replays["v1"][key], arguments.goals,
                               classify.classify_goal)
            two = step_classes(replays["v2"][key], arguments.goals,
                               classify.classify_goal, messages.get(key))
            aborted = replays["v2"][key]["outcome"] == "error"
            if aborted:
                fallback += 1
                two = one
            runs_one, runs_two = stops(one), stops(two)
            marks = []
            for name, indices in runs_one:
                if name == "unreplayed":
                    moved = (not aborted and "unreplayed" not in two)
                else:
                    moved = (not aborted and all(
                        index < len(two) and family(two[index]) != name
                        for index in indices))
                marks.append(moved)
                total_stops += 1
                by_class_total[name] += 1
                if moved:
                    covered += 1
                    by_class_covered[name] += 1
            sequences[key] = {"v1": [name for name, _ in runs_one],
                              "v2": [name for name, _ in runs_two],
                              "v2_closes": closes_at_start(two)}
            handle.write(json.dumps({
                "module": key[0], "lemma": key[1],
                "v1": [[name, indices[0], indices[-1], mark] for
                       (name, indices), mark in zip(runs_one, marks)],
                "v2": [[name, indices[0], indices[-1]]
                       for name, indices in runs_two],
                "v1_closes": closes_at_start(one),
                "v2_closes": closes_at_start(two),
                "outcome_v1": replays["v1"][key]["outcome"],
                "outcome_v2": replays["v2"][key]["outcome"]}) + "\n")
    print(f"    v2 replays aborted by a failed hand sentence: {fallback} "
          f"(v1 sequence kept)")
    print(f"    v1 stops {total_stops}; covered by v2 {covered} "
          f"({100 * covered / max(1, total_stops):.1f} %)")
    print("    by class, covered / v1 stops: " + ", ".join(
        f"{name} {by_class_covered[name]}/{count}"
        for name, count in by_class_total.most_common()))
    lengths = [len(value["v2"]) for value in sequences.values()]
    lengths.sort()
    if lengths:
        print(f"    v2 stall sequence length: median {lengths[len(lengths) // 2]}, "
              f"p90 {lengths[int(len(lengths) * 0.9)]}, max {lengths[-1]}")

    # (c) The smallest class set whose closure reaches 10 and 30 percent.
    corpus_v2 = {(row["module"], row["lemma"]): row for row in corpus["v2"]}
    closed_now = sum(1 for row in corpus["v2"] if row["outcome"] == "closed")
    bench = {key: set(value["v2"]) for key, value in sequences.items()
             if not value["v2_closes"]}
    first_of = {key: (sequences[key]["v2"] or ["closes"])[0] for key in bench}
    outside = [row for key, row in corpus_v2.items()
               if key not in sequences and row["outcome"] != "closed"]
    outside_first = collections.Counter(
        row.get("pred_class") if row["outcome"] == "residual" else row["outcome"]
        for row in outside)
    classes = sorted({name for value in bench.values() for name in value}
                     - {"unreplayed"})

    def closes(rules: set[str]) -> tuple[int, float]:
        exact = sum(1 for value in bench.values() if value <= rules)
        estimate = 0.0
        for first, count in outside_first.items():
            peers = [key for key in bench if first_of[key] == first]
            if not peers:
                continue
            rate = sum(1 for key in peers if bench[key] <= rules) / len(peers)
            estimate += rate * count
        return exact, estimate

    print(f"(c) closed now under v2: {closed_now} of {total}; "
          f"one hypothetical rule per class; benchmark exact, rest estimated")
    for excluded, target in itertools.product(((), ("raised",)), (0.10, 0.30)):
        candidates = [name for name in classes if name not in excluded]
        need = target * total
        found = None
        for size in range(0, len(candidates) + 1):
            best = None
            for chosen in itertools.combinations(candidates, size):
                exact, estimate = closes(set(chosen))
                reached = closed_now + exact + estimate
                if best is None or reached > best[0]:
                    best = (reached, chosen, exact, estimate)
            if best and best[0] >= need:
                found = (size, best)
                break
            if size >= 6 and best:
                found = (None, best)
                break
        if found and found[0] is not None:
            size, (reached, chosen, exact, estimate) = found
            print(f"    {int(target * 100)} % ({need:.0f}), without {list(excluded)}: {size} classes "
                  f"{list(chosen)}: {closed_now} + {exact} benchmark + "
                  f"{estimate:.0f} estimated = {reached:.0f}")
        elif found:
            reached, chosen, exact, estimate = found[1]
            print(f"    {int(target * 100)} % ({need:.0f}), without {list(excluded)}: not reached by 6 "
                  f"classes; best {list(chosen)} gives {reached:.0f} "
                  f"({100 * reached / total:.1f} %)")

    # (d) Rows only a restatement closes.
    residual = [key for key in bench]
    first_restate = sum(1 for key in residual if first_of[key] in RESTATEMENT)
    share = lambda n: f"{n} ({100 * n / max(1, len(residual)):.1f} %)"
    only = sum(1 for key in residual if bench[key] and bench[key] <= RESTATEMENT)
    with_wand = sum(1 for key in residual
                    if bench[key] and bench[key] <= RESTATEMENT | {"C9"})
    touches = sum(1 for key in residual if bench[key] & RESTATEMENT)
    stop_total = sum(len(value["v2"]) for key, value in sequences.items()
                     if key in bench)
    stop_restate = sum(1 for key, value in sequences.items() if key in bench
                       for name in value["v2"] if name in RESTATEMENT | {"C9"})
    print(f"(d) v2 residual benchmark lemmas {len(residual)}: first stop C6 or "
          f"C8 {share(first_restate)}; some stop C6 or C8 {share(touches)}; "
          f"every stop C6 or C8 {share(only)}; every stop C6, C8 or C9 "
          f"{share(with_wand)}; stops in C6, C8, C9 {stop_restate} of "
          f"{stop_total}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
