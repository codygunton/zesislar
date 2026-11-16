"""Refuse solver engines outside BoundedSolve in Automation2 tactics.

A solver never runs on an unbounded context: in Automation2 every micromega
call, bit-vector saturation, VM run on a goal, and raw context saturation goes
through `ZesuSsz/Automation2/BoundedSolve.v`, which prunes the context to the
goal's facts within a step bound and checks a node budget first. `lia` and
`bv_solve` stay as entry points: their global overrides in Hooks.v call the
wrapper. This check reads tactic definitions (`Ltac`, `Ltac2`,
`Tactic Notation`, `Hint Extern`) only; lemma proofs run once, at compile time,
on their fixed statements. A definition that must call an engine directly is
listed with a reason in `solver_engine_allowlist.json`.
"""
import json
import re
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "tools/block"))
from check_data_only_lemmas import rocq_commands

SCOPE = "ZesuSsz/Automation2/"
EXEMPT_PREFIXES = (
    # The wrapper itself.
    "ZesuSsz/Automation2/BoundedSolve.v",
    # The legacy umbrella (AllLegacy) is not loaded by Automation2.All.
    "ZesuSsz/Automation2/Legacy/",
)
ALLOWLIST_PATH = Path(__file__).with_name("solver_engine_allowlist.json")

# Engines: micromega, the stdpp bit-vector preparation and saturation, VM or
# native runs on a goal, the raw lia leaf, and the raw context saturations.
ENGINES = {
    "xlia", "xnlia", "xnra", "xpsatz", "nia", "nra", "psatz", "zify", "Zify.zify",
    "bv_saturate", "bv_saturate_unsigned", "bv_simplify_arith",
    "vm_compute", "native_compute",
    "zesu_lia_linear_first3", "LinearFirstLia.zesu_lia_linear_first3",
    "ZesuSsz.Automation2.LinearFirstLia.zesu_lia_linear_first3",
    "zesu_saturate_seminaive", "PureFacts.zesu_saturate_seminaive",
    "ZesuSsz.Automation2.PureFacts.zesu_saturate_seminaive",
    "ZesuSsz.Automation.PureFacts.zesu_saturate_derived_facts",
}
# `eval vm_compute in t` computes a term; only a run on a goal is an engine call.
TERM_EVALUATION = {"vm_compute", "native_compute"}
# A statement without `:=` opens a proof that runs until its closer.
TACTIC_COMMANDS = {"Ltac", "Ltac2", "Tactic", "Hint"}
PROOF_OPENERS = {"Lemma", "Theorem", "Corollary", "Fact", "Remark", "Proposition",
                 "Example", "Goal", "Instance", "Definition", "Fixpoint", "Program",
                 "Obligation", "Next", "Proof"}
PROOF_CLOSERS = {"Qed", "Defined", "Admitted", "Abort"}
ATTRIBUTE_WORDS = {"Local", "Global", "Export", "Polymorphic", "Monomorphic", "#"}


def allowlist(path=ALLOWLIST_PATH):
    data = json.loads(Path(path).read_text())
    return {(row["file"], row["name"]): row["reason"] for row in data["allowed"]}


def _head(values):
    """The command keyword after attributes, and the defined name."""
    index = 0
    while index < len(values):
        value = values[index]
        if value == "#":
            depth = 0
            index += 1
            while index < len(values):
                if values[index] == "[":
                    depth += 1
                elif values[index] == "]":
                    depth -= 1
                    if depth == 0:
                        index += 1
                        break
                index += 1
            continue
        if value in ATTRIBUTE_WORDS:
            index += 1
            continue
        break
    if index >= len(values):
        return None, None
    keyword = values[index]
    rest = values[index + 1:]
    while rest and rest[0] in ("rec", "mutable", "Set"):
        rest = rest[1:]
    if keyword == "Hint":
        return ("Hint", "Hint Extern") if rest[:1] == ["Extern"] else (None, None)
    if keyword == "Tactic":
        notation = next((value for value in rest if value.startswith('"')), '""')
        return "Tactic", "Tactic Notation " + notation
    return keyword, (rest[0].split(".")[-1] if rest else None)


def solver_engine_failures(name, text, allowed):
    """Engine calls in the tactic definitions of one Automation2 file."""
    if not name.startswith(SCOPE) or name.startswith(EXEMPT_PREFIXES):
        return []
    failures = []
    in_proof = False
    for command in rocq_commands(text):
        values = [value for value, _ in command]
        keyword, defined = _head(values)
        if keyword in PROOF_CLOSERS:
            in_proof = False
            continue
        if keyword in TACTIC_COMMANDS and not in_proof:
            if keyword in ("Ltac", "Ltac2") and defined is None:
                continue
            for index, value in enumerate(values):
                if value not in ENGINES:
                    continue
                if value in TERM_EVALUATION and index and values[index - 1] == "eval":
                    continue
                # An engine's own definition and its recursive calls.
                if value.split(".")[-1] == defined or (name, defined) in allowed:
                    continue
                line = text.count("\n", 0, command[index][1]) + 1
                failures.append(f"solver engine outside BoundedSolve: {name}:{line}: "
                                f"{value} in {defined}")
        elif keyword in PROOF_OPENERS and (keyword == "Proof" or ":=" not in values):
            in_proof = True
    return failures
