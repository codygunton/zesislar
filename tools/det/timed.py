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


def root_of(module: Path) -> Path:
    """The source tree the module belongs to.

    The A/B runner probes the same lemma in two trees whose automation
    differs, so the copy has to be generated from the tree the probe will
    compile against, not from the working directory.
    """
    for candidate in [module.resolve()] + list(module.resolve().parents):
        if (candidate / CURRENT).exists():
            return candidate
    return Path.cwd()


def source_for(module: Path) -> Path:
    """The automation the module actually uses."""
    text = module.read_text()
    return root_of(module) / (LEGACY if "Automation.AllLegacy" in text
                              else CURRENT)


def hooks_for(module: Path) -> Path:
    root = root_of(module)
    return root / (LEGACY_HOOKS if source_for(module) == root / LEGACY
                   else CURRENT_HOOKS)


def strip_comments(text: str) -> str:
    """Remove Coq comments, which nest, keeping string literals intact.

    The generated copy never needs a comment, and leaving them in is a
    trap: a comment written between two clauses of a tactic looks like the
    end of the tactic to any regular expression that hunts for one.
    """
    out, depth, index = [], 0, 0
    while index < len(text):
        if text.startswith("(*", index):
            depth += 1
            index += 2
            continue
        if text.startswith("*)", index) and depth:
            depth -= 1
            index += 2
            continue
        if not depth and text[index] == '"':
            end = text.find('"', index + 1)
            end = len(text) if end < 0 else end + 1
            out.append(text[index:end])
            index = end
            continue
        if not depth:
            out.append(text[index])
        index += 1
    return "".join(out)


def body_of(text: str, name: str) -> str:
    """The body of one `Ltac`, comments already gone."""
    found = re.search(rf"^Ltac {name} :=(.*?)(?=^Ltac |\Z)", text, re.S | re.M)
    if not found:
        raise KeyError(f"the automation defines no {name}")
    return found.group(1).rstrip().rstrip(".")


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
    body = body_of(strip_comments(LITHIUM.read_text()), "liStep")
    labelled = timed_alternatives(body, r"first\s*\[(.*?)\]", "lis", False)
    return f"Ltac liStep ::={labelled}.\n"


def timed_pass(text: str, labels: bool,
               extra_alternatives: tuple[str, ...] = ()) -> str:
    """Timed copies of the search list and of every pass that runs it.

    The current automation names the list once (`zesu_run_pass_steps`) and
    wraps it twice, as rule set v1 and as rule set v2, with
    `zesu_run_pass` choosing between them by one class lookup. The copy
    reproduces that shape, so a probe that imports rule set v2 measures
    the v2 list and a probe that does not measures v1. The legacy
    automation has one flat `zesu_run_pass` and takes the second branch.

    A candidate rule is tried in a probe before a gate is paid for, so
    `extra_alternatives` goes into the list itself, where both passes see
    it. The probe path fences each job in a 6 GiB scope, so a rule that
    opens an unbounded search kills its own probe instead of the machine.
    """
    def with_extras(body: str, close: str) -> str:
        for index, alternative in enumerate(extra_alternatives):
            entry = (f'time "new:{index:02d}_{alternative}" ({alternative})'
                     if labels else alternative)
            cut = body.rindex(close)
            body = body[:cut] + f" |\n     {entry}" + body[cut:]
        return body

    def renamed(body: str) -> str:
        for name in ("zesu_run_pass_steps", "zesu_run_pass_v1",
                     "zesu_run_pass_v2", "zesu_liAStep", "zesu_finish"):
            body = re.sub(rf"\b{name}\b(?!_)", f"{name}_timed", body)
        return body

    if "Ltac zesu_run_pass_steps :=" not in text:
        flat = timed_alternatives(body_of(text, "zesu_run_pass"),
                                  r"repeat first\s*\[(.*?)\]", "alt", True,
                                  labels)
        flat = with_extras(flat, "]; liShow")
        return f"Ltac zesu_run_pass_timed :={renamed(flat)}.\n"

    steps = timed_alternatives(body_of(text, "zesu_run_pass_steps"),
                               r"first\s*\[(.*?)\]", "alt", True, labels)
    out = f"Ltac zesu_run_pass_steps_timed :={renamed(with_extras(steps, ']'))}.\n"
    for name in ("zesu_run_pass_v1", "zesu_run_pass_v2", "zesu_run_pass"):
        out += f"Ltac {name}_timed :={renamed(body_of(text, name))}.\n"
    return out


def timed_tactics(module: Path, labels: bool = True,
                  extra_alternatives: tuple[str, ...] = ()) -> str:
    """`zesu_block_timed`: the block automation with a label on every entry.

    With `labels` false the copy keeps only the instruction counter, which
    costs one failing `lazymatch` per interpreter step. That variant measures
    how many instructions a block steps without changing what it costs.
    """
    source = source_for(module)
    text = strip_comments(source.read_text())
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
    hooks = strip_comments(hooks_for(module).read_text())
    step = timed_alternatives(body_of(hooks, "zesu_liAStep"),
                              r"first\s*\[(.*?)\]", "li", False, labels)
    step_tactic = f"Ltac zesu_liAStep_timed :={step}.\n"
    pass_tactic = timed_pass(text, labels, extra_alternatives)
    run = body_of(text, "zesu_run")
    run = re.sub(r"\bzesu_run_pass\b", "zesu_run_pass_timed", run)
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
             if source_for(module) == root_of(module) / LEGACY else
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
