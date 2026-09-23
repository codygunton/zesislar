#!/usr/bin/env python3
"""Probe one proof with the block automation and record what it leaves open.

The probe keeps the module text up to the `Proof.` of the target proof, then
replaces the hand lines with the block automation alone. What the automation
leaves is the residual goal. The original hand lines are the label, never
part of the probe.
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

from goals import conclusion, split_goals  # noqa: E402
from modules import find_proof  # noqa: E402

BEGIN = "RESIDUAL-BEGIN"
END = "RESIDUAL-END"
BLOCK_CALL = {"standard": "zesu_block.", "pure": "try zesu_block."}
# Class C4 asks which pure solver closes the goal. `assert_succeeds` runs the
# solver and then puts the goal back, so one probe tries every candidate.
SOLVERS = [("bv_solve", "bv_solve"), ("lia", "lia"),
           ("bv_simplify_lia", "bv_simplify; lia")]
SOLVER_LINE = re.compile(r"^SOLVER (?P<name>\S+)$", re.M)
# A closed proof state cannot print the end marker from inside the proof:
# `idtac` needs a goal and raises "No such goal" once the automation closed
# every one. A fresh trivial goal after `Abort.` always has one.
END_MARKER = [f'Goal True. idtac "{END}". Abort.']
ERROR_KINDS = [
    ("not_bi", re.compile(r"iStartProof: not a BI assertion")),
    ("limit_memory", re.compile(r"proof limit exceeded: memory")),
    ("no_such_goal", re.compile(r"Error: No such goal")),
    ("tactic_failure", re.compile(r"Error: Tactic failure")),
    ("compile_error", re.compile(r"^Error:", re.M)),
]


GOAL_HEADER = re.compile(r"^(?P<count>\d+) goals?(\s|$)|^1 goal(\s|$)")
NO_GOALS = re.compile(r"No more goals|This subproof is complete")
TACTIC_TIME = re.compile(r"Tactic call zesu_run ran for (?P<seconds>[0-9.]+) secs")
MAX_RSS = re.compile(r"Maximum resident set size \(kbytes\): (?P<kb>\d+)")
TIMEOUT_EXIT = 124
DEFAULT_SECONDS = 300


def limit_env(seconds: int) -> dict:
    """`coqc_scratch.sh` reads its own time limit from the environment."""
    environment = dict(os.environ)
    environment["ZESU_COQC_SECONDS"] = str(seconds)
    return environment
GOAL_TEXT_HEAD = 8 * 1024


def probe_body(solver: bool = False, variant: str = "standard") -> list[str]:
    """The probe body: the block automation, then what to print.

    `variant` "pure" wraps the automation in `try`, which keeps the goal when
    `iStartProof` refuses a plain Coq statement.
    """
    opening = f'idtac "{BEGIN}". move => *. {BLOCK_CALL[variant]}'
    if not solver:
        return [f"{opening} all: liShow. Show.", "Abort."]
    choice = "1: first [" + " | ".join(
        f'assert_succeeds ({tactic}); idtac "SOLVER {name}"'
        for name, tactic in SOLVERS) + ' | idtac "SOLVER none"].'
    return [opening, choice, "all: liShow. Show.", "Abort."]


@dataclass
class Capture:
    module: str
    lemma: str
    outcome: str
    seconds: float = 0.0
    rss_mib: int = 0
    zesu_run_seconds: list[float] = field(default_factory=list)
    goal_count: int = 0
    goal_heads: list[str] = field(default_factory=list)
    goal_text: str = ""
    goal_sha256: str = ""
    label_lines: list[str] = field(default_factory=list)
    error_lines: list[str] = field(default_factory=list)
    solver: str = ""
    error_kind: str = ""
    probe_variant: str = "standard"
    probe: str = ""
    full_goal_text: str = ""


def probe_text(module: Path, lemma: str, solver: bool = False,
               variant: str = "standard",
               imports: tuple[str, ...] = ()) -> tuple[str, list[str]]:
    """Return the probe source for `lemma` and the hand lines it replaces.

    `imports` names modules the probe should require on top of the ones
    the proof module already has. A rule that is built but not exported
    from `Automation/All.v` is measured that way: the corpus sees it
    without it being installed for every proof in the repository.
    """
    proof = find_proof(module, lemma)
    lines = module.read_text().split("\n")
    header = [f"Require Import {name}." for name in imports]
    prefix = header + lines[:proof.proof_line] + ["Proof."]
    trailer = [f"End {name}." for name in reversed(proof.open_blocks)]
    body = probe_body(solver, variant) + END_MARKER
    source = ["Set Printing Width 200."] + prefix + body + trailer + [""]
    return "\n".join(source), proof.body


def error_kind(output: str) -> str:
    for name, pattern in ERROR_KINDS:
        if pattern.search(output):
            return name
    return "unknown"


def goal_heads(goal_text: str) -> list[str]:
    """The conclusion head of each goal in a `Show` block."""
    return [head for head in (conclusion(block)
                              for block in split_goals(goal_text)) if head]


def count_goals(output: str) -> tuple[int, str]:
    """Return the goal count and the goal text that `Show` printed.

    `Show` leads with `No more goals.` for a closed proof state and with
    `N goals` otherwise. Text with neither still counts as residual: reading
    it as closed would credit the automation with a proof it did not find.
    """
    marked = output.split(BEGIN, 1)
    if len(marked) < 2:
        return 0, ""
    tail = marked[1].split(END, 1)[0]
    lines = tail.split("\n")
    for index, line in enumerate(lines):
        stripped = line.strip()
        if NO_GOALS.search(stripped):
            return 0, ""
        header = GOAL_HEADER.match(stripped)
        if header:
            count = int(header.group("count")) if header.group("count") else 1
            return count, "\n".join(lines[index + 1:]).strip("\n")
    if tail.strip():
        return len(split_goals(tail)), tail.strip("\n")
    return 0, ""


def gnu_time() -> list[str]:
    """`/usr/bin/time -v` when this machine has it; nothing when it does not.

    Without GNU time the peak memory comes from `coqc_scratch.sh`, which
    samples `VmRSS` of the compiler itself while it runs.
    """
    for candidate in ("/usr/bin/time", "/bin/time", "/usr/local/bin/time"):
        if Path(candidate).exists():
            return [candidate, "-v"]
    return []


def run_probe(probe: Path, build_dir: Path, scratch: Path,
              timeout: int = 300, cwd: Path | None = None) -> tuple[int, str, str]:
    command = [*gnu_time(), "timeout", str(timeout + 30), "nice", "-n", "10",
               "bash", str(scratch), str(probe), str(build_dir)]
    process = subprocess.run(command, capture_output=True, text=True,
                             env=limit_env(timeout), cwd=cwd)
    return process.returncode, process.stdout, process.stderr


def error_lines(output: str) -> list[str]:
    """The first 20 lines that explain why the probe stopped."""
    interesting = [line for line in output.split("\n")
                   if line.strip() and not line.startswith("\t")
                   and "Command being timed" not in line
                   and not MAX_RSS.match(line.strip())]
    marked = [index for index, line in enumerate(interesting)
              if line.lstrip().startswith("Error")
              or "proof limit exceeded" in line]
    start = max(0, marked[0] - 1) if marked else max(0, len(interesting) - 20)
    return interesting[start:start + 20]


def capture(module: Path, lemma: str, build_dir: Path,
            scratch: Path, probe_dir: Path, solver: bool = False,
            variant: str = "standard",
            seconds: int = DEFAULT_SECONDS,
            imports: tuple[str, ...] = (), cwd: Path | None = None) -> Capture:
    source, label_lines = probe_text(module, lemma, solver, variant, imports)
    probe_dir.mkdir(parents=True, exist_ok=True)
    suffix = ("__solver" if solver else "") + (
        "" if variant == "standard" else f"__{variant}")
    probe = probe_dir / f"{module.stem}__{lemma}{suffix}.v"
    probe.write_text(source)
    started = time.monotonic()
    code, stdout, stderr = run_probe(probe, build_dir, scratch, seconds, cwd)
    wall = time.monotonic() - started
    output = stdout + "\n" + stderr

    seconds = 0.0
    timing = re.search(r"exit=(-?\d+) ms=(\d+) rss_kb=(\d+)", stdout)
    if timing:
        seconds = int(timing.group(2)) / 1000.0
    rss = MAX_RSS.search(stderr)
    rss_mib = int(rss.group("kb")) // 1024 if rss else 0
    if not rss_mib and timing:
        rss_mib = int(timing.group(3)) // 1024
    run_seconds = [float(match.group("seconds"))
                   for match in TACTIC_TIME.finditer(output)]

    result = Capture(module=module.name, lemma=lemma, outcome="error",
                     seconds=seconds or round(wall, 3), rss_mib=rss_mib,
                     zesu_run_seconds=run_seconds, label_lines=label_lines,
                     probe=str(probe))
    reached_end = END in output
    count, goal_text = count_goals(output)
    if code == TIMEOUT_EXIT or "proof limit exceeded: time" in stderr:
        result.outcome = "timeout"
    elif reached_end and count:
        result.outcome = "residual"
    elif reached_end:
        result.outcome = "closed"
    if result.outcome in {"residual", "closed"}:
        result.goal_count = count
        result.full_goal_text = goal_text
        result.goal_text = goal_text[:GOAL_TEXT_HEAD]
        result.goal_sha256 = hashlib.sha256(goal_text.encode()).hexdigest()
        result.goal_heads = goal_heads(goal_text)
    else:
        result.error_lines = error_lines(output)
        result.error_kind = ("timeout" if result.outcome == "timeout"
                             else error_kind(output))
    result.probe_variant = ("solver " if solver else "") + variant
    found = SOLVER_LINE.search(output)
    if found:
        result.solver = found.group("name")
    return result


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("module", type=Path)
    parser.add_argument("lemma")
    parser.add_argument("--build-dir", type=Path, required=True)
    parser.add_argument("--scratch", type=Path,
                        default=Path("tools/coqc_scratch.sh"))
    parser.add_argument("--probe-dir", type=Path, default=None)
    parser.add_argument("--print-probe", action="store_true")
    parser.add_argument("--solver", action="store_true",
                        help="run the class C4 solver probe instead")
    parser.add_argument("--variant", default="standard",
                        choices=sorted(BLOCK_CALL),
                        help="probe body to use")
    arguments = parser.parse_args()
    if arguments.print_probe:
        print(probe_text(arguments.module, arguments.lemma,
                         arguments.solver, arguments.variant)[0])
        return 0
    probe_dir = arguments.probe_dir or arguments.build_dir / "residuals" / "probes"
    result = capture(arguments.module, arguments.lemma,
                     arguments.build_dir, arguments.scratch, probe_dir,
                     arguments.solver, arguments.variant)
    record = {key: value for key, value in result.__dict__.items()
              if key != "full_goal_text"}
    print(json.dumps(record))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
