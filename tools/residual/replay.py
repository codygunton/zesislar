#!/usr/bin/env python3
"""Replay a hand proof and find every line the automation could replace.

Phase 1 recorded one residual per proof: the first place the automation
stops. A proof of twelve lines can hide four more stops behind that one.
This replay applies the original proof one sentence at a time and, at each
state, asks the block automation to finish the rest.

The probe never changes the proof state it measures. `assert_succeeds` runs
the automation and then puts the state back, so one compilation walks the
whole proof. `Undo` would do the same, but Rocq replays the document from
the start for every `Undo` in batch mode, which is quadratic.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import os
import subprocess
import sys
import time
from dataclasses import dataclass, field
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

from classify import classify  # noqa: E402
from modules import find_proof  # noqa: E402
from sentences import opener_and_steps  # noqa: E402

BEGIN = "REPLAY-BEGIN"
END = "REPLAY-END"
AUTOMATION = "zesu_block"
# Seconds one automation call may take at one state.
STEP_SECONDS = 30
MARKER = re.compile(r"^(?P<kind>CLOSES|STOP|FAILED|GOAL) (?P<index>\d+)"
                    r"(?P<rest>.*)$")
MESSAGE = re.compile(r"^(?P<kind>ERRMSG|RAN) (?P<index>\d+)"
                     r"(?:\s*\|\s*(?P<text>.*))?$")
# Ltac1 cannot hand a tactic's error text to the script, and `Fail` prints
# nothing in batch mode. Ltac2 can catch the exception and print it, so the
# message probe reports why the automation stopped at each state.
MESSAGE_PREAMBLE = [
    "From Ltac2 Require Import Ltac2.",
    'Set Default Proof Mode "Classic".',
    "Ltac2 zesu_report (name : string) (run : unit -> unit) :=",
    "  match Control.case run with",
    '  | Val _ => Message.print (Message.concat (Message.of_string "RAN ")',
    "                             (Message.of_string name))",
    "  | Err e => Message.print (Message.concat",
    '               (Message.concat (Message.of_string "ERRMSG ")',
    '                  (Message.of_string name))',
    '               (Message.concat (Message.of_string " | ")',
    "                  (Message.of_exn e)))",
    "  end.",
]
TIMEOUT_EXIT = 124
DEFAULT_SECONDS = 300


def limit_env(seconds: int) -> dict:
    """`coqc_scratch.sh` reads its own time limit from the environment."""
    environment = dict(os.environ)
    environment["ZESU_COQC_SECONDS"] = str(seconds)
    return environment
GOAL_HEAD = 8 * 1024
# A sentence may open with a goal selector; the tactic is what follows.
SELECTOR = re.compile(r"^\s*(?:all|\d+(?:-\d+)?(?:\s*,\s*\d+)*)\s*:\s*")
TACTIC_HEAD = re.compile(r"^\(*\s*(?P<head>[A-Za-z_][\w']*|[-+*{}]+)")


def check_line(index: int, seconds: int = STEP_SECONDS) -> str:
    """The probe that asks whether the automation finishes from here.

    Two guards make the walk affordable. `once` stops Ltac backtracking into
    the automation when the outer test fails: without it a single failing
    check explores every alternative inside `zesu_run` and never returns.
    `timeout` bounds one call, so a slow state costs its own budget and not
    the whole proof.

    Branch order matters. The first branch answers the question and costs one
    run of the automation. The second only runs when the first failed, and it
    prints what the automation left. The third records a state where the
    automation raised or ran past its budget.
    """
    call = f"once (timeout {seconds} {AUTOMATION})"
    return (f"all: first "
            f"[assert_succeeds ({call}; fail); idtac \"CLOSES {index}\" "
            f"|assert_succeeds ({call}; try liShow; "
            f"lazymatch goal with |- ?g => idtac \"GOAL {index}\" g end); "
            f"idtac \"STOP {index}\" "
            f"|idtac \"FAILED {index}\"].")


def message_line(index: int, seconds: int = STEP_SECONDS) -> str:
    """Ask why the automation stops here, without disturbing the state."""
    return (f"all: assert_succeeds (ltac2:(zesu_report \"{index}\" "
            f"(fun () => ltac1:(once (timeout {seconds} {AUTOMATION})))))."
            )


def replay_text(module: Path, lemma: str,
                messages: bool = False) -> tuple[str, list[str], list[str]]:
    """The replay source, the opener sentences, and the step sentences."""
    proof = find_proof(module, lemma)
    opener, steps = opener_and_steps("\n".join(proof.body))
    lines = module.read_text().split("\n")
    source = ["Set Printing Width 200."] + lines[:proof.proof_line]
    if messages:
        source.extend(MESSAGE_PREAMBLE)
    source.append("Proof.")
    source.append(f'idtac "{BEGIN}".')
    source.extend(opener)
    source.append(message_line(0) if messages else check_line(0))
    for index, sentence in enumerate(steps, start=1):
        source.append(sentence)
        source.append(message_line(index) if messages else check_line(index))
    source.append("Abort.")
    source.extend(f"End {name}." for name in reversed(proof.open_blocks))
    source.append(f'Goal True. idtac "{END}". Abort.')
    return "\n".join(source) + "\n", opener, steps


@dataclass
class Step:
    index: int
    tactic: str = ""
    closes: bool = False
    failed: bool = False
    goals: list[str] = field(default_factory=list)


@dataclass
class Replay:
    module: str
    lemma: str
    outcome: str = "error"
    seconds: float = 0.0
    rss_mib: int = 0
    n_lines: int = 0
    n_sentences: int = 0
    closes_at: int | None = None
    steps_reached: int = 0
    messages: dict = field(default_factory=dict)
    steps: list[Step] = field(default_factory=list)
    error_lines: list[str] = field(default_factory=list)


def parse_markers(output: str, count: int) -> list[Step]:
    """One `Step` per index, gathering every marker the probe printed."""
    steps = {index: Step(index=index) for index in range(count)}
    pending: tuple[int, list[str]] | None = None
    for line in output.split("\n"):
        found = MARKER.match(line)
        if found is None:
            if pending is not None:
                pending[1].append(line)
            continue
        if pending is not None:
            index, chunk = pending
            steps[index].goals.append("\n".join(chunk).strip())
            pending = None
        index = int(found.group("index"))
        if index not in steps:
            continue
        kind = found.group("kind")
        if kind == "CLOSES":
            steps[index].closes = True
        elif kind == "FAILED":
            steps[index].failed = True
        elif kind == "GOAL":
            pending = (index, [found.group("rest").strip()])
    if pending is not None:
        index, chunk = pending
        steps[index].goals.append("\n".join(chunk).strip())
    return [steps[index] for index in sorted(steps)]


def parse_messages(output: str) -> dict:
    """The failure message the automation raised at each step, by index.

    A Rocq message wraps over several lines, so a line-based read keeps
    only its first line and loses the goal the message names. The text runs
    until the next marker.
    """
    found: dict[str, str] = {}
    current: str | None = None
    chunk: list[str] = []
    for line in output.split("\n"):
        marked = MESSAGE.match(line.strip())
        if marked is None:
            if current is not None:
                chunk.append(line.strip())
            continue
        if current is not None:
            found[current] = " ".join(part for part in chunk if part).strip()
        if marked.group("kind") == "RAN":
            found[marked.group("index")] = ""
            current, chunk = None, []
            continue
        current = marked.group("index")
        chunk = [(marked.group("text") or "").strip()]
    if current is not None:
        found[current] = " ".join(part for part in chunk if part).strip()
    return found


def first_closing(steps: list[Step]) -> int | None:
    """The first state from which the automation finished the whole proof."""
    for step in steps:
        saw_marker = step.closes or step.failed or step.goals
        if step.closes and not step.failed and not step.goals and saw_marker:
            return step.index
    return None


def run(module: Path, lemma: str, build_dir: Path, scratch: Path,
        probe_dir: Path, goal_dir: Path,
        timeout: int = DEFAULT_SECONDS, messages: bool = False) -> Replay:
    source, opener, steps = replay_text(module, lemma, messages)
    probe_dir.mkdir(parents=True, exist_ok=True)
    suffix = "__messages" if messages else "__replay"
    probe = probe_dir / f"{module.stem}__{lemma}{suffix}.v"
    probe.write_text(source)
    started = time.monotonic()
    process = subprocess.run(
        ["timeout", str(timeout + 30), "nice", "-n", "10", "bash",
         str(scratch), str(probe), str(build_dir)],
        capture_output=True, text=True, env=limit_env(timeout))
    wall = time.monotonic() - started
    output = process.stdout + "\n" + process.stderr

    proof = find_proof(module, lemma)
    result = Replay(module=module.name, lemma=lemma,
                    n_lines=len([line for line in proof.body if line.strip()]),
                    n_sentences=len(steps) + len(opener))
    timing = re.search(r"exit=(-?\d+) ms=(\d+) rss_kb=(\d+)", process.stdout)
    result.seconds = (int(timing.group(2)) / 1000.0 if timing
                      else round(wall, 3))
    result.rss_mib = int(timing.group(3)) // 1024 if timing else 0

    if process.returncode == TIMEOUT_EXIT \
            or "proof limit exceeded: time" in process.stderr:
        result.outcome = "timeout"
    elif END in output:
        result.outcome = "replayed"
    if result.outcome == "error":
        result.error_lines = [line for line in output.split("\n")
                              if line.strip().startswith("Error")][:20]
        if not result.error_lines:
            result.error_lines = output.strip().split("\n")[-8:]
        return result

    # A timeout still carries the steps it reached. Those say whether the
    # probe diverged at one state or simply ran out of budget late in a long
    # proof, which are different faults with different remedies.
    marked = output.split(BEGIN, 1)[-1].split(END, 1)[0]
    if messages:
        # The probe output is the record here, so keep it beside the goals.
        goal_dir.mkdir(parents=True, exist_ok=True)
        (goal_dir / f"{probe.stem}.log").write_text(output)
        result.messages = parse_messages(marked)
        return result
    result.steps = parse_markers(marked, len(steps) + 1)
    for step in result.steps:
        if step.index:
            step.tactic = tactic_head(steps[step.index - 1])
        goal_dir.mkdir(parents=True, exist_ok=True)
        for text in step.goals:
            digest = hashlib.sha256(text.encode()).hexdigest()
            (goal_dir / f"{digest}.txt").write_text(text)
    result.closes_at = first_closing(result.steps)
    result.steps_reached = sum(
        1 for step in result.steps
        if step.closes or step.failed or step.goals)
    return result


def tactic_head(sentence: str) -> str:
    """The tactic name of a sentence, past any goal selector."""
    text = SELECTOR.sub("", sentence.strip())
    found = TACTIC_HEAD.match(text)
    return found.group("head") if found else text[:24]


def record(result: Replay) -> dict:
    """The replay as one JSON object, with a class for every residual."""
    steps = []
    for step in result.steps:
        classes, digests = [], []
        for text in step.goals:
            classes.append(classify(text[:GOAL_HEAD]).pred_class)
            digests.append(hashlib.sha256(text.encode()).hexdigest())
        steps.append({"index": step.index, "tactic": step.tactic,
                      "closes": step.closes, "failed": step.failed,
                      "goals": len(step.goals), "classes": classes,
                      "goal_sha256": digests,
                      "goal_head": [text.split("\n")[0][:120]
                                    for text in step.goals]})
    return {"module": result.module, "lemma": result.lemma,
            "outcome": result.outcome, "seconds": result.seconds,
            "rss_mib": result.rss_mib, "n_lines": result.n_lines,
            "n_sentences": result.n_sentences, "closes_at": result.closes_at,
            "steps_reached": result.steps_reached,
            "messages": result.messages,
            "steps": steps, "error_lines": result.error_lines}


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("module", type=Path)
    parser.add_argument("lemma")
    parser.add_argument("--build-dir", type=Path,
                        default=Path("_build/agents/corpus"))
    parser.add_argument("--scratch", type=Path,
                        default=Path("tools/coqc_scratch.sh"))
    parser.add_argument("--print-probe", action="store_true")
    arguments = parser.parse_args()
    if arguments.print_probe:
        print(replay_text(arguments.module, arguments.lemma)[0])
        return 0
    result = run(arguments.module, arguments.lemma, arguments.build_dir,
                 arguments.scratch,
                 arguments.build_dir / "residuals" / "probes",
                 arguments.build_dir / "residuals")
    print(json.dumps(record(result)))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
