"""WP1 probes: the frame a proof search sees, and where its seconds go.

Two probe shapes share the module prefix that `tools/residual/capture.py`
builds. The frame probe stops after the block automation introduces and
atomizes the precondition, so it prints the context without paying for the
search. The profile probe runs the whole block automation under `Ltac
Profiling` and prints the tactic tree.

Both keep the module text up to the target `Proof.` and drop the hand lines,
exactly as the corpus probe does. Neither edits a proof.
"""

from __future__ import annotations

import os
import re
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "residual"))

from modules import find_proof  # noqa: E402

import timed  # noqa: E402

BEGIN = "PROBE-BEGIN"
END = "PROBE-END"

# The introduction phase of the block automation, whatever the module's own
# `zesu_block` is: the legacy automation and the current one introduce
# differently, so the probe stubs out the search and calls the module's own
# block tactic rather than inlining one of the two.
STUB = "Ltac zesu_run ::= idtac."

# The frame grows as the interpreter steps, so it is not a fixed property of
# a lemma: it is only comparable at a fixed budget. 600 steps costs a few
# seconds and reaches the wide frames the expensive probes work in.
STEPS = int(os.environ.get("ZESU_DET_STEPS", 600))

# `all:` keeps the probe working when the block automation closed the proof
# (no goal left) or left more than one goal, which a bare `do` refuses.
STEPPED_BODY = [
    f'idtac "{BEGIN}".',
    "try intros.",
    "try zesu_block.",
    f"all: try (do {STEPS} (try zesu_liAStep)).",
    "all: try liShow.",
    "Show.",
    "Abort.",
]

# A closed proof state cannot print from inside the proof, so the end marker
# lives on a fresh trivial goal, as in the corpus probe.
END_MARKER = [f'Goal True. idtac "{END}". Abort.']

# The real proof, timed, so the report can name the `Qed` cost of a lemma
# beside the cost of finding its proof. The body comes from the module.
QED_BODY: list[str] = []

TIMED_BODY = [
    f'idtac "{BEGIN}".',
    "try intros.",
    "try zesu_block_timed.",
    "Abort.",
]

# The module text up to the target `Proof.`, compiled and then abandoned.
# That is what every probe pays before its automation runs at all, and it
# depends on where in the module the lemma sits, so it is measured per
# lemma rather than taken from the module's compile cost.
PREFIX_BODY = [
    f'idtac "{BEGIN}".',
    "Abort.",
]

# `counted` is `timed` without the labels: the same copy of the automation,
# so the same instruction count, at the cost of one failing `lazymatch` per
# interpreter step instead of a timer on every entry.
COUNTED_BODY = TIMED_BODY

BODIES = {"stepped": STEPPED_BODY, "qed": QED_BODY, "timed": TIMED_BODY,
          "counted": COUNTED_BODY, "prefix": PREFIX_BODY}


def probe_text(module: Path, lemma: str, shape: str) -> str:
    """The probe source for `lemma`, with the hand lines dropped.

    The module text up to the target `Proof.` is kept, so the probe sees
    exactly the context the real proof sees. Nothing is written back.
    """
    proof = find_proof(module, lemma)
    lines = module.read_text().split("\n")
    head = lines[:proof.declaration_line]
    if shape == "stepped":
        # `liShow` and the ssreflect intro patterns come from Islaris; a
        # module that states only pure facts imports neither, and a missing
        # reference is a parse-time error that `try` cannot catch.
        head = ["Require Import isla.isla."] + head + [STUB]
    if shape in {"timed", "counted"}:
        head = (timed.requires(module) + head
                + timed.timed_tactics(module,
                                      labels=shape == "timed").split("\n"))
    prefix = head + lines[proof.declaration_line:proof.proof_line] + ["Proof."]
    trailer = [f"End {name}." for name in reversed(proof.open_blocks)]
    body = BODIES[shape]
    if shape == "qed":
        body = [f'idtac "{BEGIN}".'] + proof.body + ["Time Qed."]
    source = (["Set Printing Width 200."] + prefix + body
              + END_MARKER + trailer + [""])
    return "\n".join(source)


# --- reading what the probes print -------------------------------------

TOTAL_TIME = re.compile(r"^\s*total time:\s+([0-9.]+)s", re.M)
# One row of the `Show Ltac Profile` tree:
#   ─name ------------------   1.2%  34.5%     17    0.123s
ROW = re.compile(
    r"^(?P<indent>[^a-zA-Z]*?)(?P<name>[A-Za-z_][^\s]*(?: [^\s-]+)*?)"
    r"\s*-+\s+(?P<local>[0-9.]+)%\s+(?P<total>[0-9.]+)%\s+"
    r"(?P<calls>\d+)\s+(?P<max>[0-9.]+)s\s*$")


SECTION = re.compile(r"^\s*tactic\s+local\s+total\s+calls\s+max")


def profile_rows(output: str) -> tuple[float, list[dict]]:
    """The profiled total seconds and one record per tactic.

    `Show Ltac Profile` prints the flat ranking first and the call tree
    second, under the same header. The flat ranking already aggregates the
    self time of each tactic, so reading past its end would count every
    tactic twice.
    """
    found = TOTAL_TIME.search(output)
    total = float(found.group(1)) if found else 0.0
    lines = output.split("\n")
    headers = [index for index, line in enumerate(lines) if SECTION.match(line)]
    if headers:
        stop = headers[1] if len(headers) > 1 else len(lines)
        lines = lines[headers[0]:stop]
    rows = []
    for line in lines:
        match = ROW.match(line.rstrip())
        if not match:
            continue
        rows.append({"name": match.group("name").strip(),
                     "local": float(match.group("local")),
                     "total": float(match.group("total")),
                     "calls": int(match.group("calls")),
                     "max": float(match.group("max"))})
    return total, rows


def marked(output: str) -> str:
    """What the probe printed between its two markers."""
    if BEGIN not in output:
        return ""
    return output.split(BEGIN, 1)[1].split(END, 1)[0]
