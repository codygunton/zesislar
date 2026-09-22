#!/usr/bin/env python3
"""Row 2: a boundary predicate, written from what the automation holds.

At a junction the automation holds a context. That context *is* the
boundary predicate of the segment that ends there and of the segment that
starts there, so neither has to be written by hand. This turns a probe
record whose outcome is `reached` into Coq source:

- one definition, the spatial hypotheses joined with `∗`;
- the automation's own local names closed as existentials, so the
  definition mentions only the segment's binders;
- `LithiumUnfold`, so the search can look inside it;
- optionally `Global Opaque` with its `_unfold` lemma and the
  `ZesuSealed` coverage instance the C3 rule reads, when the boundary is
  wider than rule 20's twelve conjuncts and has to be sealed.

The persistent hypotheses are not part of the boundary. They are the code
premise and the call premises, which the segment statement already names.
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent / "residual"))

from goals import COQ_RULE, IRIS_RULE  # noqa: E402

HYPOTHESIS = re.compile(r'^(?P<name>_|"[^"]*"|[A-Za-z_][\w\'’]*)\s*:\s*(?P<body>.*)$')
RULE_20_CONJUNCTS = 12
# The names a segment statement already binds. Anything else the context
# mentions was introduced by the automation and becomes an existential.
STANDARD_BINDERS = ("Sigma", "islaG0", "H", "Decoded",
                    "WriteSuccessMemoryRepresentation0")


def sections(block: str) -> tuple[list[tuple[str, str]], list[str], list[str]]:
    """The Coq context, the persistent hypotheses, the spatial ones."""
    coq: list[tuple[str, str]] = []
    persistent: list[str] = []
    spatial: list[str] = []
    target = coq
    lines = block.split("\n")
    pending: list[str] = []

    def flush(into) -> None:
        if not pending:
            return
        text = " ".join(part.strip() for part in pending)
        match = HYPOTHESIS.match(text)
        if match is None:
            pending.clear()
            return
        if into is coq:
            into.append((match.group("name"), match.group("body").strip()))
        else:
            into.append(match.group("body").strip())
        pending.clear()

    for line in lines:
        stripped = line.strip()
        if COQ_RULE.match(stripped):
            flush(target)
            target = persistent
            continue
        if IRIS_RULE.match(stripped):
            flush(target)
            target = spatial if stripped.endswith("□") else None
            if target is None:
                break
            continue
        if HYPOTHESIS.match(stripped) and (pending or True):
            flush(target)
            pending.append(stripped)
        elif pending:
            pending.append(stripped)
    if target is not None:
        flush(target)
    return coq, persistent, spatial


def free_locals(coq: list[tuple[str, str]], binders: str) -> list[tuple[str, str]]:
    """The Coq variables the automation introduced, in order.

    Anything the segment's own binder string already names stays a
    parameter of the boundary; the rest is existentially closed, because
    a boundary cannot mention a name that only exists inside a proof.
    """
    named = set(re.findall(r"[A-Za-z_][\w']*", binders)) | set(STANDARD_BINDERS)
    out = []
    for name, kind in coq:
        if name in named or name.startswith("_"):
            continue
        if kind.startswith(("islaG", "threadG", "WriteSuccessMemoryRepresentation")):
            continue
        out.append((name, kind))
    return out


def explicit_arguments(binders: str) -> str:
    """The names a definition with these binders is applied to.

    Only the explicit groups, `(a b : T)`. The backtick groups are
    instance arguments and the braces are implicit, and both are left to
    inference, which is what every hand-written boundary in the project
    does too.
    """
    names: list[str] = []
    depth = 0
    current = ""
    implicit = False
    for index, character in enumerate(binders):
        if character == "(" and not (index and binders[index - 1] == "`"):
            depth += 1
            if depth == 1:
                current = ""
                implicit = False
                continue
        elif character == "(" :
            implicit = True
            depth += 1
            continue
        elif character == ")":
            depth -= 1
            if depth == 0 and not implicit:
                names += current.split(":")[0].split()
            continue
        if depth >= 1:
            current += character
    return " ".join(names)


def boundary_source(name: str, binders: str, coq: list[tuple[str, str]],
                    spatial: list[str], seal: bool) -> str:
    locals_ = free_locals(coq, binders)
    pure = [f"⌜{kind}⌝" for variable, kind in locals_ if kind == "Prop"]
    existentials = "".join(
        f"∃ {variable} : {kind},\n   " for variable, kind in locals_
        if kind != "Prop")
    body = " ∗\n   ".join(spatial + pure) if (spatial or pure) else "True"
    raw = f"{name}Raw" if seal else name
    applied = explicit_arguments(binders)
    lines = [
        f"Definition {raw}",
        f"    {binders} : iProp Sigma :=",
        f"  ({existentials}{body})%I.",
        f"Global Instance : LithiumUnfold (@{raw}) := I.",
    ]
    if seal:
        # Rule 20: a boundary a reader has to hold in their head shows at
        # most twelve conjuncts. A wider one is sealed, and the C3 rule
        # opens it lazily when a lookup needs what is inside.
        lines += [
            "",
            f"Definition {name}",
            f"    {binders} : iProp Sigma := {raw} {applied}.",
            "",
            f"Lemma {name}_unfold",
            f"    {binders} :",
            f"  {name} {applied} ⊣⊢ {raw} {applied}.",
            "Proof. done. Qed.",
            "",
            f"Global Opaque {name}.",
        ]
    return "\n".join(lines) + "\n"


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--records", type=Path, required=True,
                        help="probe records; only `reached` ones are used")
    parser.add_argument("--name", default=None,
                        help="the boundary's name; default from the lemma")
    parser.add_argument("--binders", default=None,
                        help="the binders the boundary keeps as parameters")
    parser.add_argument("--out", type=Path, required=True)
    arguments = parser.parse_args()

    emitted = []
    for line in arguments.records.read_text().split("\n"):
        line = line.strip()
        if not line.startswith("{"):
            continue
        record = json.loads(line)
        if record.get("outcome") != "reached" or "context" not in record:
            continue
        coq, _persistent, spatial = sections(record["context"])
        stem = arguments.name or (
            "".join(part.capitalize() for part in
                    record["lemma"].split("_")[:6]) + "Boundary")
        binders = arguments.binders or record.get("binders", "")
        emitted.append(boundary_source(
            stem, binders, coq, spatial,
            seal=len(spatial) > RULE_20_CONJUNCTS))
        print(f"{record['lemma']}: {len(spatial)} conjuncts, "
              f"{'sealed' if len(spatial) > RULE_20_CONJUNCTS else 'open'}")
    if not emitted:
        print("no record reached its exit; nothing to write", file=sys.stderr)
        return 1
    arguments.out.parent.mkdir(parents=True, exist_ok=True)
    arguments.out.write_text(
        "(* Generated by tools/det/gen_boundary.py. Do not edit. *)\n\n"
        + "\n\n".join(emitted))
    print(f"written to {arguments.out}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
