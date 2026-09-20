"""A timed copy of the block automation, derived from the automation source.

`Show Ltac Profile` cannot measure this automation: Coq's profiler raises
"invalid stack (wrong self node)" as soon as Lithium backtracks into a
profiled tactic, which every proof that steps an instruction does. The
`time` tactical has no such problem, prints for a failed call as well as a
successful one, and is exact about which entry paid.

So the probe compiles a copy of `zesu_finish`, `zesu_run_pass` and
`zesu_block` in which every finisher entry and every alternative of the
search loop carries its own `time` label. Generating the copy from the
source keeps it in step with the automation it measures, including the
rewrite WP2 makes.
"""

from __future__ import annotations

import os
import re
from pathlib import Path

CURRENT = Path("ZesuSsz/Automation/Finish.v")
LEGACY = Path("ZesuSsz/Automation/Legacy/Finish.v")
CURRENT_HOOKS = Path("ZesuSsz/Automation/Hooks.v")
# Lithium's own interpreter step. The probe redefines it with a label on
# every alternative, which is how WP1 tells `liFindInContext` apart from the
# rest of Lithium's search. Nothing is written back to the sources.
LITHIUM = Path(os.environ.get(
    "ZESU_LITHIUM_SOURCE",
    str(Path.home() / "islaris/_opam/.opam-switch/sources"
        / "coq-lithium.dev.2024-09-11.0.7945a29d/theories/lithium"
        / "interpreter.v")))
LEGACY_HOOKS = Path("ZesuSsz/Automation/Legacy/Hooks.v")
ASM_MARK = "INSTR-ASM"
PRE_MARK = "INSTR-PRE"
LABEL = re.compile(r"Tactic call (?P<label>[a-z]+:[^ ]*) ran for "
                   r"(?P<seconds>[0-9.]+) secs.*?\((?P<outcome>success|failure)")
IDENTIFIER = re.compile(r"[A-Za-z_][A-Za-z0-9_']*")
OPENERS = {"(", "["}
CLOSERS = {")", "]"}

COUNTER = f"""Ltac zesu_count_instr :=
  lazymatch goal with
  | |- envs_entails _ (WPasm tnil) => idtac "{ASM_MARK}"
  | |- envs_entails _ (instr_pre' _ _ _) => idtac "{PRE_MARK}"
  end; fail.
"""


def source_for(module: Path) -> Path:
    """The automation the module actually uses."""
    text = module.read_text()
    return LEGACY if "Automation.AllLegacy" in text else CURRENT


def hooks_for(module: Path) -> Path:
    return (LEGACY_HOOKS if source_for(module) == LEGACY else CURRENT_HOOKS)


COMMENT = re.compile(r"\(\*.*?\*\)\s*\Z", re.S)


def body_of(text: str, name: str) -> str:
    """The body of one `Ltac`, without the comment that follows it.

    The slice runs to the next `Ltac`, so a comment written between two
    tactics lands after the terminating full stop and would be spliced
    inside the generated copy.
    """
    found = re.search(rf"^Ltac {name} :=(.*?)(?=^Ltac |\Z)", text, re.S | re.M)
    if not found:
        raise KeyError(f"the automation defines no {name}")
    body = found.group(1)
    while True:
        stripped = COMMENT.sub("", body).rstrip()
        if stripped == body.rstrip():
            break
        body = stripped
    return body.rstrip().rstrip(".")


def split_top(text: str, separator: str) -> list[str]:
    """Split on `separator` at nesting depth zero.

    Brackets nest, and so does `match`/`lazymatch`, which `end` closes.
    """
    parts, depth, current = [], 0, []
    for token in re.findall(r"[A-Za-z_][A-Za-z0-9_']*|.", text, re.S):
        if token in OPENERS:
            depth += 1
        elif token in CLOSERS:
            depth -= 1
        elif token in {"match", "lazymatch", "multimatch"}:
            depth += 1
        elif token == "end":
            depth -= 1
        if token == separator and depth == 0:
            parts.append("".join(current))
            current = []
            continue
        current.append(token)
    parts.append("".join(current))
    return [part for part in parts if part.strip()]


def label_of(clause: str, index: int, kind: str) -> str:
    names = IDENTIFIER.findall(clause)
    skip = {"try", "timeout", "first", "solve", "repeat", "progress",
            "lazymatch", "goal", "with", "unshelve", "do", "time"}
    name = next((word for word in names if word not in skip), f"clause{index}")
    return f"{kind}:{index:02d}_{name}"[:60]


def timed_clauses(body: str, kind: str, labels: bool = True) -> str:
    if not labels:
        return body.strip()
    clauses = split_top(body, ";")
    return ";\n  ".join(
        f'time "{label_of(clause, index, kind)}" ({clause.strip()})'
        for index, clause in enumerate(clauses))


def timed_alternatives(body: str, pattern: str, kind: str,
                       counter: bool, labels: bool = True) -> str:
    """Put one `time` label on every alternative of a `first [ ... ]` list."""
    found = re.search(pattern, body, re.S)
    if not found:
        raise KeyError(f"no `{pattern}` in the tactic body")
    if not labels and not counter:
        return body
    alternatives = split_top(found.group(1), "|")
    entries = ["zesu_count_instr"] if counter else []
    entries += [(f'time "{label_of(alt, index, kind)}" ({alt.strip()})'
                 if labels else alt.strip())
                for index, alt in enumerate(alternatives)]
    opener = found.group(0)[:found.group(0).index("[") + 1]
    return (body[:found.start()] + opener + " |\n     ".join(entries) + "]"
            + body[found.end():])


def timed_lithium_step() -> str:
    """A copy of Lithium's `liStep` with one label per alternative."""
    if not LITHIUM.exists():
        return ""
    body = body_of(LITHIUM.read_text(), "liStep")
    labelled = timed_alternatives(body, r"first\s*\[(.*?)\]", "lis", False)
    return f"Ltac liStep ::={labelled}.\n"


def timed_tactics(module: Path, labels: bool = True) -> str:
    """`zesu_block_timed`: the block automation with a label on every entry.

    With `labels` false the copy keeps only the instruction counter, which
    costs one failing `lazymatch` per interpreter step. That variant measures
    how many instructions a block steps without changing what it costs.
    """
    source = source_for(module)
    text = source.read_text()
    # The finisher is a dispatch now, so its branches carry the labels and
    # the dispatch itself only routes. The legacy automation still has one
    # flat body, which the same code labels as a single branch.
    branches = [name for name in ("zesu_finish_normalize",
                                  "zesu_finish_entailment",
                                  "zesu_finish_pure_goal")
                if f"Ltac {name} :=" in text]
    finish = ""
    for name in branches:
        kind = {"zesu_finish_normalize": "nrm",
                "zesu_finish_entailment": "ent",
                "zesu_finish_pure_goal": "fin"}[name]
        finish += (f"Ltac {name}_timed :=\n  "
                   + timed_clauses(body_of(text, name), kind, labels) + ".\n")
    if branches and "Ltac zesu_finish_dispatch :=" in text:
        dispatch = body_of(text, "zesu_finish_dispatch")
        for name in branches:
            dispatch = re.sub(rf"\b{name}\b(?!_)", f"{name}_timed", dispatch)
        finish += f"Ltac zesu_finish_dispatch_timed :={dispatch}.\n"
        branches = branches + ["zesu_finish_dispatch"]
    body = body_of(text, "zesu_finish")
    if branches:
        for name in branches:
            body = re.sub(rf"\b{name}\b(?!_)", f"{name}_timed", body)
        finish += f"Ltac zesu_finish_timed :={body}.\n"
    else:
        finish += ("Ltac zesu_finish_timed :=\n  "
                   + timed_clauses(body, "fin", labels) + ".\n")
    hooks = hooks_for(module).read_text()
    step = timed_alternatives(body_of(hooks, "zesu_liAStep"),
                              r"first\s*\[(.*?)\]", "li", False, labels)
    step_tactic = f"Ltac zesu_liAStep_timed :={step}.\n"
    run_pass = timed_alternatives(body_of(text, "zesu_run_pass"),
                                  r"repeat first\s*\[(.*?)\]", "alt", True,
                                  labels)
    run_pass = re.sub(r"\bzesu_liAStep\b(?!_)", "zesu_liAStep_timed", run_pass)
    run_pass = run_pass.replace("zesu_finish)", "zesu_finish_timed)")
    run_pass = re.sub(r"\bzesu_finish\b(?!_)", "zesu_finish_timed", run_pass)
    pass_tactic = f"Ltac zesu_run_pass_timed :={run_pass}.\n"
    run = body_of(text, "zesu_run")
    run = run.replace("zesu_run_pass", "zesu_run_pass_timed")
    run = re.sub(r"\bzesu_finish\b(?!_)", "zesu_finish_timed", run)
    run_tactic = f"Ltac zesu_run_timed :={run}.\n"
    block = body_of(text, "zesu_block")
    block = re.sub(r"\bzesu_run\b(?!_)", "zesu_run_timed", block)
    if labels:
        # The block tactic's shape is not fixed -- it is a `tryif` now -- so
        # the labels wrap the run where it is named and the whole block
        # around it. The introduction phase is the difference.
        block = re.sub(r"\bzesu_run_timed\b",
                       'time "phase:run" (zesu_run_timed)', block)
        block_tactic = (f"Ltac zesu_block_timed :=\n"
                        f'  time "phase:block" ({block.strip()}).\n')
    else:
        block_tactic = f"Ltac zesu_block_timed :=\n  {block.strip()}.\n"
    lithium = timed_lithium_step() if labels else ""
    return (COUNTER + lithium + finish + step_tactic + pass_tactic
            + run_tactic + block_tactic)


def requires(module: Path) -> list[str]:
    """What the copy needs that the module may not import."""
    header = [line for line in source_for(module).read_text().split("\n")
              if line.startswith(("Require ", "From "))]
    header += [line for line in hooks_for(module).read_text().split("\n")
               if line.startswith(("Require ", "From "))]
    names = (["ZesuSsz.Automation.Legacy.Finish",
              "ZesuSsz.Automation.Legacy.Hooks"]
             if source_for(module) == LEGACY else
             ["ZesuSsz.Automation.Finish", "ZesuSsz.Automation.Hooks"])
    return (["From iris.proofmode Require Import environments.",
             "Require Import isla.isla."]
            + [line.replace("Require Export", "Require Import")
               for line in header]
            + [f"Require Import {name}." for name in names])


def measurements(output: str) -> dict:
    """Seconds and calls per label, and the instruction count."""
    totals: dict[str, dict] = {}
    for match in LABEL.finditer(output):
        label = match.group("label")
        entry = totals.setdefault(label, {"seconds": 0.0, "calls": 0,
                                          "failures": 0})
        entry["seconds"] += float(match.group("seconds"))
        entry["calls"] += 1
        entry["failures"] += match.group("outcome") == "failure"
    for entry in totals.values():
        entry["seconds"] = round(entry["seconds"], 3)
    return {"labels": totals,
            "instructions": output.count(ASM_MARK),
            "instr_pre": output.count(PRE_MARK)}
