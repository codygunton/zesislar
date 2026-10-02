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

HYPOTHESIS = re.compile(r'^(?P<name>_|"[^"]*"|[A-Za-z_][\w\'’]*(?:\s*,\s*[A-Za-z_][\w\'’]*)*)\s*:\s*(?P<body>.*)$')
RULE_20_CONJUNCTS = 12
# The names a segment statement already binds. Anything else the context
# mentions was introduced by the automation and becomes an existential.
STANDARD_BINDERS = ("Sigma", "islaG0", "H", "Decoded",
                    "WriteSuccessMemoryRepresentation0")
TMP_REGISTERS = ("x5", "x6", "x7", "x28", "x29", "x30", "x31")


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
    for index, atom in enumerate(atoms):
        if not atom.startswith("reg_col ["):
            continue
        entries = [re.fullmatch(r'\s*\(KindReg "(x\d+)", (.+)\)\s*', entry)
                   for entry in atom[len("reg_col ["):-1].split(";")]
        if (len(entries) == len(TMP_REGISTERS) and all(entries)
                and {entry[1] for entry in entries} == set(TMP_REGISTERS)):
            shapes = {entry[1]: entry[2] for entry in entries}
            normalized = ("reg_col (zip_with (fun r shape => (KindReg r, shape)) "
                          "tmp_registers [" + "; ".join(shapes[r] for r in TMP_REGISTERS) + "])")
            return atoms[:index] + [normalized] + atoms[index + 1:]
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


def preserve_register_precision(atoms: list[str], unknown: set[str]) -> list[str]:
    """Keep entry-unknown registers at BitsShape precision in a successor."""
    result = []
    for atom in atoms:
        direct = re.match(r'^"(x\d+)"\s*↦ᵣ\s+', atom)
        if direct and direct[1] in unknown:
            atom = f'reg_col [(KindReg "{direct[1]}", BitsShape 64)]'
        elif atom.startswith("reg_col ["):
            entries = atom[len("reg_col ["):-1].split(";")
            for index, entry in enumerate(entries):
                register = re.match(r'\s*\(KindReg "(x\d+)"', entry)
                if register and register[1] in unknown:
                    entries[index] = f'(KindReg "{register[1]}", BitsShape 64)'
            atom = "reg_col [" + "; ".join(entry.strip() for entry in entries) + "]"
        elif "tmp_registers" in atom and "zip_with" in atom:
            start, end = atom.rfind("["), atom.rfind("]")
            shapes = atom[start + 1:end].split(";")
            shapes = ["BitsShape 64" if register in unknown else shape.strip()
                      for register, shape in zip(TMP_REGISTERS, shapes)]
            atom = atom[:start + 1] + "; ".join(shapes) + atom[end:]
        result.append(atom)
    return result


def deduplicate_register_shapes(atoms: list[str]) -> list[str]:
    """Retain exact ownership and remove its explicit BitsShape duplicate."""
    exact = {match[1] for atom in atoms
             if (match := re.match(r'^"(x\d+)"\s*↦ᵣ\s+', atom))}
    for atom in atoms:
        exact.update(re.findall(r'KindReg "(x\d+)", ExactShape', atom))
        if "tmp_registers" in atom and "zip_with" in atom:
            shapes = atom[atom.rfind("[") + 1:atom.rfind("]")].split(";")
            exact.update(register for register, shape in zip(TMP_REGISTERS, shapes)
                         if "ExactShape" in shape)
    result = []
    for atom in atoms:
        if atom.startswith("reg_col ["):
            entries = atom[len("reg_col ["):-1].split(";")
            entries = [entry.strip() for entry in entries
                       if not ((match := re.fullmatch(
                           r'\s*\(KindReg "(x\d+)", BitsShape 64\)\s*', entry))
                               and match[1] in exact)]
            atom = "reg_col [" + "; ".join(entries) + "]"
        result.append(atom)
    return result


def strip_internal_handoffs(atoms: list[str], start: int, end: int) -> list[str]:
    """Remove instruction premises inside the measured CFG block."""
    def internal(atom: str) -> bool:
        match = re.match(r'instr_(?:pre|body)\s+(\([^)]*\)|0x[0-9a-fA-F]+|\d+)\s', atom)
        if not match:
            return False
        address = match[1].strip("() ")
        # Printed concrete addresses use either a numeral or a numeral plus offset.
        terms = re.fullmatch(r'(0x[0-9a-fA-F]+|\d+)(?:\s*\+\s*(\d+))?', address)
        if not terms:
            return False
        pc = int(terms[1], 0) + (int(terms[2]) if terms[2] else 0)
        return start <= pc < end
    return [atom for atom in atoms if not internal(atom)]


def complete_register_file(atoms: list[str]) -> list[str]:
    """Add shapes for missing general registers without replacing ownership."""
    owned: set[str] = set()
    for atom in atoms:
        registers = []
        if atom.startswith("reg_col "):
            if not (atom.startswith("reg_col [") or "tmp_registers" in atom
                    or atom == "reg_col zesu_ram_sys_regs"
                    or atom.startswith(("reg_col match ", "reg_col (match "))):
                raise ValueError(f"unexpanded register collection: {atom}")
            registers = re.findall(r'KindReg "(x\d+)"', atom)
            if "tmp_registers" in atom:
                registers += list(TMP_REGISTERS)
            if not registers and atom not in ("reg_col zesu_ram_sys_regs", "reg_col []"):
                raise ValueError(f"unexpanded register collection: {atom}")
        else:
            match = re.match(r'^"(x\d+)"\s*↦ᵣ', atom)
            if match:
                registers = [match.group(1)]
        for register in registers:
            if register in owned:
                raise ValueError(f"duplicate register resource: {register}")
            owned.add(register)
    missing = [f'(KindReg "x{index}", BitsShape 64)'
               for index in range(1, 32) if f"x{index}" not in owned]
    return atoms + (["reg_col [" + "; ".join(missing) + "]"] if missing else [])


def flat_state_tactics(prefix: str, root: Path) -> str:
    """Expand loaded project packages in a proof-mode capture.

    Coq elaborates the reductions. Source text supplies constant names only.
    The capture retains abstract frame parameters and does not split arrays.
    """
    loaded: dict[str, str] = {}
    pending = [prefix]
    imports = re.compile(
        r"(?:From\s+([\w.]+)\s+)?Require\s+(?:Import|Export)\s+"
        r"([^;]+?)\.(?=\s|$)")
    while pending:
        source = re.sub(r"\(\*.*?\*\)", "", pending.pop(), flags=re.S)
        for match in imports.finditer(source):
            for name in match[2].split():
                module = (match[1] + "." if match[1] else "") + name
                path = root / (module.replace(".", "/") + ".v")
                if path.exists() and module not in loaded:
                    loaded[module] = path.read_text()
                    pending.append(loaded[module])
    tactics = []
    for module, source in [("", prefix), *loaded.items()]:
        for name in re.findall(r"(?:Definition|Fixpoint)\s+(\w+)\b", source):
            if not any(part in name.lower() for part in
                       ("frame", "scratch", "handoff", "event", "stack", "register", "untouched", "tailwords", "memory", "slots")):
                continue
            constant = (module + "." if module else "") + name
            unfold = name + "_unfold"
            action = ("rewrite " + (module + "." if module else "") + unfold
                      if re.search(r"Lemma\s+" + re.escape(unfold) + r"\b", source)
                      else "unfold " + constant)
            tactics.append(
                "iMatchHyp ltac:(fun H P => "
                "iEval (progress " + action + ") in H)")
    return ("all: repeat first [" + " |\n".join(tactics) + "].\n") if tactics else ""


def entry_witness_binders(binders: str, coq: list[tuple[str, str]],
                          sorts: dict[str, str]) -> tuple[str, str]:
    """Name captured entry witnesses in the block's parameter list."""
    variables, _facts = local_parts(free_locals(coq, binders), sorts, True)
    expanded = binders + "".join(f" ({name} : {kind})" for name, kind in variables)
    return expanded, explicit_arguments(expanded)


def substitute_witnesses(coq: list[tuple[str, str]], spatial: list[str],
                         witnesses: dict[str, str]) -> tuple[list[tuple[str, str]], list[str]]:
    """Use probe-recorded witnesses instead of fresh existential variables."""
    known = {name for name, _kind in coq}
    unknown = set(witnesses) - known
    if unknown:
        raise ValueError("witnesses absent from probe: " + ", ".join(sorted(unknown)))
    def replace(text: str) -> str:
        for name, expression in witnesses.items():
            text = re.sub(r"(?<![\w'])" + re.escape(name) + r"(?![\w'])",
                          lambda _match: "(" + expression + ")", text)
        return text
    return ([(name, replace(kind)) for name, kind in coq if name not in witnesses],
            [replace(atom) for atom in spatial])


def require_call_resources(atoms: list[str]) -> None:
    """Reject missing ownership. Never add inferred resources."""
    if "reg_col zesu_ram_sys_regs" not in atoms:
        raise ValueError("missing top-level reg_col zesu_ram_sys_regs")
    if not any(atom.startswith("reg_col ") and "tmp_registers" in atom
               for atom in atoms):
        declared = set()
        for atom in atoms:
            direct = re.match(r'^"(x\d+)"\s*↦ᵣ', atom)
            if direct:
                declared.add(direct[1])
            elif atom.startswith("reg_col "):
                declared.update(re.findall(r'KindReg "(x\d+)"', atom))
        # Keep mixed and conditional collections exactly as captured.
        # A generated proof must establish the required branch ownership.
        if not set(TMP_REGISTERS).issubset(declared):
            raise ValueError("missing top-level temporary register collection")


def require_open_resources(atoms: list[str], binders: str) -> None:
    """Reject folded packages until inference exposes their resource atoms."""
    abstract = {name for name, kind in binder_types(binders).items()
                if kind == "iProp Sigma"}
    for atom in atoms:
        if (atom in abstract or atom in ("True", "emp")
                or atom.startswith(("reg_col ", "spec_trace ", "mmio_range ",
                                    "instr_pre ", "instr_body ", "⌜"))
                or (atom.startswith("∀ ") and "instr_pre " in atom)
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
        elif sort == "Type" or not strict:
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
    has_square_rule = any(IRIS_RULE.match(line.strip()) and line.strip().endswith("□")
                          for line in lines)
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
            into.extend((name.strip(), match.group("body").strip())
                        for name in match.group("name").split(","))
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
        if HYPOTHESIS.match(stripped):
            flush(target)
            if target is persistent and not has_square_rule and stripped.startswith("_ :"):
                # A goal without persistent hypotheses omits the square rule.
                target = spatial
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
                    witnesses: dict[str, str] | None = None) -> str:
    coq, spatial = substitute_witnesses(coq, spatial, witnesses or {})
    spatial = [atom for body in spatial for atom in spatial_atoms(body)]
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
            sorts=record.get("local_sorts", record.get("sorts"))))
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
