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
from gen_coverage import memory_range  # noqa: E402

HYPOTHESIS = re.compile(r'^(?P<name>_|"[^"]*"|[A-Za-z_][\w\'’]*)\s*:\s*(?P<body>.*)$')
RULE_20_CONJUNCTS = 12
# The names a segment statement already binds. Anything else the context
# mentions was introduced by the automation and becomes an existential.
STANDARD_BINDERS = ("Sigma", "islaG0", "H", "Decoded",
                    "WriteSuccessMemoryRepresentation0")
TMP_REGISTERS = ("x5", "x6", "x7", "x28", "x29", "x30", "x31")
COQ_LOCALS = re.compile(r"^([A-Za-z_][\w'’]*(?:\s*,\s*[A-Za-z_][\w'’]*)*)\s*:\s*(.*)$")


def spatial_atoms(body: str) -> list[str]:
    """Split only outer separating conjunctions. Preserve binder scopes."""
    body = body.strip()
    if body.endswith("%I"):
        body = body[:-2].strip()
    depth, quoted = 0, False
    cuts = []
    for index, character in enumerate(body):
        if character == '"':
            quoted = not quoted
        if quoted:
            continue
        if character in "([{⌜":
            depth += 1
        elif character in ")]}⌝":
            depth -= 1
        elif character == "∗" and depth == 0 and body[index - 1:index] != "ₘ":
            # A wand or a register predicate binds the following chain.
            prefix = body[:index]
            if "-" == body[index - 1:index] or "↦ᵣ:" in prefix or re.match(r"∃\b|∃", prefix):
                return [body]
            cuts.append(index)
    if body.startswith("(") and body.endswith(")"):
        depth = 0
        for index, character in enumerate(body):
            depth += (character == "(") - (character == ")")
            if depth == 0:
                if index == len(body) - 1:
                    return spatial_atoms(body[1:-1])
                break
    if not cuts:
        return [body]
    return [part for start, end in zip([-1] + cuts, cuts + [len(body)])
            for part in spatial_atoms(body[start + 1:end])]


def normalize_temporaries(atoms: list[str]) -> list[str]:
    """Collect all seven exact temporary atoms without changing values."""
    if any(atom.startswith("reg_col ") and "tmp_registers" in atom
           for atom in atoms):
        return atoms
    expanded = []
    for atom in atoms:
        match = re.fullmatch(r"reg_col\s*\[(.*)\]", atom, re.DOTALL)
        if match is None:
            expanded.append(atom)
            continue
        parts, start, depth = [], 0, 0
        body = match.group(1)
        for index, character in enumerate(body):
            depth += (character in "([{") - (character in ")]}")
            if character == ";" and depth == 0:
                parts.append(body[start:index].strip())
                start = index + 1
        parts.append(body[start:].strip())
        resources = []
        for part in parts:
            pair = re.fullmatch(r'\(KindReg "(x\d+)",\s*(.+)\)', part, re.DOTALL)
            if pair is None:
                break
            register, shape = pair.groups()
            exact = re.fullmatch(r"ExactShape\s*\((.+)\)", shape, re.DOTALL)
            if exact:
                resources.append(f'"{register}" ↦ᵣ {exact.group(1)}')
            elif re.fullmatch(r"BitsShape\s+\d+", shape):
                resources.append(f'"{register}" ↦ᵣ: λ v, ⌜valu_has_shape v ({shape})⌝ ∗ True')
            else:
                break
        else:
            expanded.extend(resources)
            continue
        expanded.append(atom)
    atoms = expanded
    found = {}
    for index, atom in enumerate(atoms):
        match = re.fullmatch(r'"(x\d+)"\s*↦ᵣ\s+(.+)', atom)
        if match and match.group(1) in TMP_REGISTERS:
            register = match.group(1)
            if register in found:
                raise ValueError(f"duplicate temporary resource: {register}")
            found[register] = index, f"ExactShape ({match.group(2)})"
            continue
        match = re.fullmatch(
            r'"(x\d+)"\s*↦ᵣ:\s*(?:fun\s+(\w+)\s*=>|λ\s+(\w+)\s*,)\s*'
            r'⌜valu_has_shape\s+(\w+)\s+\((BitsShape\s+\d+)\)⌝\s*∗\s*True', atom)
        if match and match.group(1) in TMP_REGISTERS:
            register, bound = match.group(1), match.group(2) or match.group(3)
            if match.group(4) != bound:
                continue
            if register in found:
                raise ValueError(f"duplicate temporary resource: {register}")
            found[register] = index, match.group(5)
    if len(found) != len(TMP_REGISTERS):
        return atoms
    shapes = "; ".join(f"({found[register][1]})" for register in TMP_REGISTERS)
    collection = ("reg_col (zip_with (fun r shape => (KindReg r, shape)) "
                  f"tmp_registers [{shapes}])")
    indices = {index for index, _ in found.values()}
    return [collection] + [atom for index, atom in enumerate(atoms)
                           if index not in indices]


def normalize_lent_arrays(atoms: list[str]) -> list[str]:
    """Apply a captured array-return wand to its owned slice."""
    atoms = list(atoms)
    while True:
        for index, atom in enumerate(atoms):
            if atom.count("-∗") != 1 or any(term in atom for term in ("∃", "λ", "fun ")):
                continue
            borrowed, restored = (part.strip() for part in atom.split("-∗"))
            if borrowed.count("↦ₘ∗") != 1 or restored.count("↦ₘ∗") != 1:
                continue
            owner = next((other for other, resource in enumerate(atoms)
                          if other != index and resource == borrowed), None)
            if owner is not None:
                atoms = [resource for other, resource in enumerate(atoms)
                         if other not in (index, owner)] + spatial_atoms(restored)
                break
        else:
            return atoms


def normalize_bitvector_addresses(atoms: list[str], widths: dict[str, int]) -> list[str]:
    """Restore captured address widths before elaborating unsigned numerals."""
    def replace(match):
        value = match.group(1)
        width = widths.get(value)
        if not isinstance(width, int) or width <= 0:
            raise ValueError(f"missing captured bit width for unsigned numeral: {value}")
        return f"bv_unsigned (BV {width} {value})"
    return [re.sub(r"bv_unsigned\s+(\d+)(?:%bv)?\b", replace, atom)
            for atom in atoms]


def normalize_memory_literals(atoms: list[str], widths: dict[str, int]) -> list[str]:
    """Restore the captured bit width that Rocq omits from word numerals."""
    def ungroup(address: str) -> str:
        while address.startswith("(") and address.endswith(")"):
            depth = 0
            for index, character in enumerate(address):
                depth += (character == "(") - (character == ")")
                if depth == 0:
                    break
            if index != len(address) - 1:
                break
            address = address[1:-1].strip()
        return address

    def captured_width(address: str) -> int | None:
        return next((width for key, width in widths.items()
                     if ungroup(key) == ungroup(address)), None)

    normalized = []
    for atom in atoms:
        for event in reversed(list(re.finditer(r"SWriteMem\s+", atom))):
            start = event.end()
            end = start
            if atom[start] == "(":
                depth = 1
                end += 1
                while depth and end < len(atom):
                    depth += (atom[end] == "(") - (atom[end] == ")")
                    end += 1
            else:
                while end < len(atom) and not atom[end].isspace():
                    end += 1
            value = re.match(r"\s+(\d+)%bv\b", atom[end:])
            if value is not None:
                address = atom[start:end]
                width = captured_width(address)
                if not isinstance(width, int) or width <= 0:
                    raise ValueError(f"missing captured bit width for write event: {address}")
                atom = (atom[:end] + f" (BV {width} {value.group(1)})"
                        + atom[end + value.end():])
        array = re.fullmatch(r"(.+?)\s*↦ₘ∗\s*(\[[^\[\]]*\])", atom)
        if array is not None and re.search(r"\d+%bv\b", array.group(2)):
            address, values = array.groups()
            width = captured_width(address)
            if not isinstance(width, int) or width <= 0:
                raise ValueError(f"missing captured bit width for memory array: {atom}")
            values = re.sub(r"(\d+)%bv\b", lambda value:
                            f"(BV {width} {value.group(1)})", values)
            atom = f"{address} ↦ₘ∗ {values}"
        match = re.fullmatch(r"(.+?)\s*↦ₘ\s*(\d+)(?:%bv)?", atom)
        if match is None:
            normalized.append(atom)
            continue
        address, value = match.groups()
        width = captured_width(address)
        if not isinstance(width, int) or width <= 0:
            raise ValueError(f"missing captured bit width for memory word: {atom}")
        normalized.append(f"{address} ↦ₘ (BV {width} {value})")
    return normalized


def require_call_resources(atoms: list[str]) -> None:
    """Reject missing ownership. Never add inferred resources."""
    if "reg_col zesu_ram_sys_regs" not in atoms:
        raise ValueError("missing top-level reg_col zesu_ram_sys_regs")
    if not any(atom.startswith("reg_col ") and "tmp_registers" in atom
               for atom in atoms):
        raise ValueError("missing top-level temporary register collection")


def require_open_resources(atoms: list[str], binders: str) -> None:
    """Reject folded packages until inference exposes their resource atoms."""
    abstract = {name for name, kind in binder_types(binders).items()
                if kind == "iProp Sigma"}
    for atom in atoms:
        if (atom in abstract or atom in ("True", "emp")
                or atom.startswith(("reg_col ", "spec_trace ", "mmio_range ",
                                    "instr_pre ", "instr_body ", "⌜"))
                or re.match(r'"[^"]+"\s*(?:#\s*"[^"]+"\s*)?↦ᵣ', atom)):
            continue
        if "↦ₘ" in atom:
            base = atom.split("↦ₘ", 1)[0]
            depth = sum((character in "([{⌜") - (character in ")]}⌝")
                        for character in base)
            if depth == 0:
                continue
        raise ValueError(f"folded or unsupported spatial resource: {atom}")


def binder_types(binders: str) -> dict[str, str]:
    """Read explicit parameter types, including nested parentheses."""
    out = {}
    for match in re.finditer(r"\(([A-Za-z_][\w' ]*)\s*:\s*", binders):
        depth = 1
        for index in range(match.end(), len(binders)):
            depth += (binders[index] == "(") - (binders[index] == ")")
            if depth == 0:
                kind = binders[match.end():index].strip()
                out.update({name: kind for name in match.group(1).split()})
                break
    return out


def local_parts(locals_: list[tuple[str, str]], sorts: dict[str, str],
                strict: bool) -> tuple[list[tuple[str, str]], list[str]]:
    """Separate proof facts from values using recorded or known sorts."""
    variables, facts = [], []
    propositions = {variable for variable, kind in locals_ if kind == "Prop"}
    known_types = r"(?:Prop|Type|Set|Z|nat|N|bool|string|valu|spec|isla_trace|unit|bv\s+\d+|list\s+.+)"
    for variable, kind in locals_:
        sort = sorts.get(variable)
        if strict and sort is None:
            raise ValueError(f"missing Coq sort for local {variable}: {kind}")
        if sort is None:
            if kind in propositions or kind in ("True", "False"):
                sort = "Prop"
            elif re.fullmatch(known_types, kind):
                sort = "Type"
            elif re.search(r" = | ≠ | < | <= | ≤ | > | >= | ≥ | /\\ | \\/ | ↔ ", kind):
                # Equality and arithmetic relations are propositions. Do not
                # infer the sort of a function or a dependent product here.
                if not any(operator in kind for operator in ("->", "→", "forall", "∀")):
                    sort = "Prop"
        if sort == "Prop":
            facts.append(f"⌜{kind}⌝")
        elif sort in ("Set", "Type") or not strict:
            variables.append((variable, kind))
        else:
            raise ValueError(f"missing Coq sort for local {variable}: {kind}")
    return variables, facts


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
        if into is coq:
            match = COQ_LOCALS.match(text)
            if match is not None:
                coq.extend((name.strip(), match.group(2).strip())
                           for name in match.group(1).split(","))
            pending.clear()
            return
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
        if HYPOTHESIS.match(stripped) or (target is coq and COQ_LOCALS.match(stripped)):
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
                    spatial: list[str], seal: bool, *,
                    call_resources: bool = False,
                    sorts: dict[str, str] | None = None,
                    memory_word_widths: dict[str, int] | None = None) -> str:
    spatial = [atom for body in spatial for atom in spatial_atoms(body)]
    spatial = normalize_memory_literals(spatial, memory_word_widths or {})
    spatial = normalize_lent_arrays(spatial)
    if call_resources:
        spatial = normalize_temporaries(spatial)
        require_call_resources(spatial)
        require_open_resources(spatial, binders)
    locals_, pure = local_parts(free_locals(coq, binders), sorts or {}, call_resources)
    existentials = "".join(
        f"∃ {variable} : {kind},\n   " for variable, kind in locals_
    )
    # Only direct memory atoms with known coverage can enter the seal.
    # A folded state, a continuation, or an unknown memory size stays open.
    kinds = dict(coq)
    kinds.update(binder_types(binders))
    memory, ranges, opened = [], [], []
    for atom in spatial:
        coverage = (memory_range(atom, kinds)
                    if "↦ᵣ" not in atom and "spec_trace" not in atom
                    and not atom.startswith(("∃", "⌜", "reg_col"))
                    and "-∗" not in atom else None)
        if seal and coverage:
            memory.append(atom)
            ranges.append(coverage)
        else:
            opened.append(atom)
    applied = explicit_arguments(binders)
    lines = []
    if memory:
        frame = f"{name}Memory"
        raw = f"{frame}Raw"
        frame_binders = binders + "".join(
            f" ({variable} : {kind})" for variable, kind in locals_)
        frame_args = " ".join([applied] + [variable for variable, kind in locals_]).strip()
        body = " ∗\n   ".join([f"({atom})" for atom in memory] + ["True"])
        lines += [
            f"Definition {raw}",
            f"    {frame_binders} : iProp Sigma := ({body})%I.",
            f"Global Instance : LithiumUnfold (@{raw}) := I.",
            f"Global Typeclasses Opaque {raw}.",
            f"Definition {frame}",
            f"    {frame_binders} : iProp Sigma := {raw} {frame_args}.",
            f"Lemma {frame}_unfold {frame_binders} :",
            f"  {frame} {frame_args} ⊣⊢ {raw} {frame_args}.",
            "Proof. done. Qed.",
            f"Global Opaque {frame}.",
            f"Global Instance zesu_sealed_{frame} {frame_binders} :",
            f"  ZesuSealed ({frame} {frame_args}) ({raw} {frame_args})",
            f"    [{'; '.join(ranges)}] [] := {frame}_unfold {frame_args}.",
            "",
        ]
        opened.append(f"{frame} {frame_args}")
    # Parentheses keep each register predicate's lambda inside its atom.
    body = " ∗\n   ".join([f"({atom})" for atom in opened + pure] + ["True"])
    lines += [f"Definition {name}", f"    {binders} : iProp Sigma :=",
              f"  ({existentials}{body})%I.",
              f"Global Instance : LithiumUnfold (@{name}) := I.",
              f"Global Typeclasses Opaque {name}."]
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
    parser.add_argument("--call-resources", action="store_true",
                        help="require top-level system and temporary collections")
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
        spatial = [atom for resource in spatial for atom in spatial_atoms(resource)]
        if arguments.call_resources:
            spatial = normalize_temporaries(spatial)
        stem = arguments.name or (
            "".join(part.capitalize() for part in
                    record["lemma"].split("_")[:6]) + "Boundary")
        binders = arguments.binders or record.get("binders", "")
        emitted.append(boundary_source(
            stem, binders, coq, spatial,
            seal=len(spatial) > RULE_20_CONJUNCTS,
            call_resources=arguments.call_resources,
            sorts=record.get("local_sorts", record.get("sorts")),
            memory_word_widths=record.get("memory_word_widths")))
        print(f"{record['lemma']}: {len(spatial)} conjuncts, "
              f"{'sealed' if len(spatial) > RULE_20_CONJUNCTS else 'open'}")
    if not emitted:
        print("no record reached its exit; nothing to write", file=sys.stderr)
        return 1
    arguments.out.parent.mkdir(parents=True, exist_ok=True)
    arguments.out.write_text(
        "(* Generated by tools/det/gen_boundary.py. Do not edit. *)\n\n"
        "Require Import ZesuSsz.Automation.All.\n"
        "Require Import ZesuSsz.Automation.SealedCoverage.\n\n"
        + "\n\n".join(emitted))
    print(f"written to {arguments.out}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
