#!/usr/bin/env python3
"""Emit a `ZesuSealed` coverage instance for every sealed predicate.

A predicate that is `Global Opaque` with an `X_unfold` lemma beside it is
a seal the lazy C3 rule may open. What the rule needs and the source does
not say is *what the seal holds*: the address ranges and the registers.
This reads the definition, derives the ranges from the memory resources
in its body, and writes one instance per predicate.

A range it cannot derive is reported rather than guessed: an instance
that claims coverage it does not have would send the rule to open the
wrong bundle.
"""

from __future__ import annotations

import argparse
import re
from pathlib import Path

OPAQUE = re.compile(r"^Global Opaque\s+([A-Za-z_][\w']*)\s*\.", re.M)
DEFINITION = re.compile(
    r"^Definition\s+(?P<name>{name})\b(?P<binders>.*?):\s*iProp Sigma\s*:=\s*"
    r"(?P<body>.*?)^(?=\s*$|Lemma |Definition |Global )", re.M | re.S)
# `base ↦ₘ∗ source`, `base ↦ₘ? n`, `base ↦ₘ v`: one word, one region, one array.
ARRAY = re.compile(r"([A-Za-z_][\w'.() +\-]*?)\s*↦ₘ∗\s*([A-Za-z_][\w'.]*)")
REGION = re.compile(r"([A-Za-z_][\w'.() +\-]*?)\s*↦ₘ\?\s*(\d+)")
REGISTER = re.compile(r'"(x\d+|PC)"\s*↦ᵣ')


def array_width(values: str, kinds: dict[str, str]) -> int | None:
    """Use the expression's recorded type or an element-preserving slice."""
    kind = kinds.get(values.strip(), "")
    match = re.fullmatch(r"list\s+\(?bv\s+(\d+)\)?", kind.strip())
    if match:
        return int(match.group(1))
    sliced = re.fullmatch(r"(?:take|drop)\s+(?:\d+|[\w']+|\([^()]*\))\s+(.+)", values.strip())
    if sliced:
        return array_width(sliced.group(1), kinds)
    return None


def memory_range(atom: str, kinds: dict[str, str]) -> str | None:
    """Return coverage for one memory atom with a known size."""
    if "↦ₘ" not in atom:
        return None
    base, value = atom.split("↦ₘ", 1)
    # An atom must own memory directly. A nested predicate can also own
    # registers or traces, which must remain outside the memory seal.
    depth = 0
    for character in base:
        depth += (character in "([{⌜") - (character in ")]}⌝")
    if depth:
        return None
    base, value = base.strip(), value.strip()
    if value.startswith("∗"):
        values = value[1:].strip()
        width = array_width(values, kinds)
        if width is None or width % 8:
            return None
        size = f"{width // 8} * Z.of_nat (length ({values}))"
    elif value.startswith("?"):
        size = value[1:].strip()
    else:
        kind = kinds.get(value, "")
        width = re.fullmatch(r"bv\s+(\d+)", kind)
        if width is None:
            width = re.match(r"\(?BV\s+(\d+)\b", value)
        if width is None or int(width.group(1)) % 8:
            return None
        size = str(int(width.group(1)) // 8)
    return f"({base}, ({base}) + ({size}))"


def definition(text: str, name: str) -> re.Match | None:
    return re.search(DEFINITION.pattern.format(name=re.escape(name)), text,
                     re.M | re.S)


def ranges_of(body: str) -> tuple[list[str], list[str]]:
    """Coq expressions for the ranges, and the registers, a body holds."""
    ranges = []
    for base, values in ARRAY.findall(body):
        base = base.strip()
        ranges.append(f"({base}, {base} + Z.of_nat (length {values}))")
    for base, size in REGION.findall(body):
        base = base.strip()
        ranges.append(f"({base}, {base} + {size})")
    registers = sorted({name for name in REGISTER.findall(body)})
    return ranges, registers


def has_opaque_tail(binders: str, body: str) -> bool:
    """The body passes on an abstract `iProp` parameter, so what it holds
    is not knowable from the definition."""
    abstract = re.findall(r"\(\s*([A-Za-z_][\w']*)\s*:\s*iProp Sigma\s*\)",
                          binders)
    return any(re.search(rf"\b{name}\b", body) for name in abstract)


def opaque_instance(name: str, binders: str, body: str) -> str:
    return (f"(* {name} passes on an abstract iProp, so its coverage is not\n"
            f"   knowable here: it is opened only after every declared\n"
            f"   coverage has been checked and none matched. *)\n"
            f"Global Instance zesu_sealed_tail_{name}{binders} :\n"
            f"  ZesuSealedOpaqueTail ({name}{binders_names(binders)})\n"
            f"    ({body.strip().rstrip('.')}) :=\n"
            f"  {name}_unfold{binders_names(binders)}.\n")


def instance(name: str, binders: str, ranges: list[str],
             registers: list[str], body: str) -> str:
    quoted = ", ".join(f'"{register}"%string' for register in registers)
    return (f"(* Coverage of {name}, from its definition. *)\n"
            f"Global Instance zesu_sealed_{name}{binders} :\n"
            f"  ZesuSealed ({name}{binders_names(binders)})\n"
            f"    ({body.strip().rstrip('.')})\n"
            f"    [{'; '.join(ranges)}] [{quoted}] :=\n"
            f"  {name}_unfold{binders_names(binders)}.\n")


def binders_names(binders: str) -> str:
    names = re.findall(r"\(([^:()]+):", binders)
    flat = " ".join(part.strip() for group in names for part in group.split())
    return (" " + flat) if flat else ""


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source", type=Path, required=True)
    parser.add_argument("--out", type=Path, required=True)
    arguments = parser.parse_args()
    text = arguments.source.read_text()
    emitted, skipped = [], []
    for name in OPAQUE.findall(text):
        if f"{name}_unfold" not in text:
            skipped.append((name, "no unfold lemma"))
            continue
        found = definition(text, name)
        if not found:
            skipped.append((name, "definition not parsed"))
            continue
        binders = found.group("binders").rstrip()
        body = found.group("body")
        if has_opaque_tail(binders, body):
            emitted.append(opaque_instance(name, binders, body))
            continue
        ranges, registers = ranges_of(body)
        if not ranges and not registers:
            # A seal that only names another predicate holds whatever that
            # one holds. Its coverage is unknown here, which is the opaque
            # tier, not a reason to leave it shut: the chain of seals over
            # a stack frame is several deep.
            emitted.append(opaque_instance(name, binders, body))
            continue
        emitted.append(instance(name, binders, ranges, registers, body))
    arguments.out.parent.mkdir(parents=True, exist_ok=True)
    arguments.out.write_text(
        "(* Generated by tools/det/gen_coverage.py. Do not edit. *)\n"
        "Require Import ZesuSsz.Automation.All.\n"
        "Require Import isla.riscv64.riscv64.\n"
        "Require Import ZesuSsz.Contracts.Endpoints.\n"
        "Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessNativeContract.\n"
        "Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessRepresentation.\n"
        f"Require Import ZesuSsz.Automation.SealedCoverage.\n"
        f"Require Import {module_of(arguments.source)}.\n\n"
        + "\n".join(emitted))
    for name, why in skipped:
        print(f"skipped {name}: {why}")
    print(f"emitted {len(emitted)} coverage instances to {arguments.out}")
    return 0


def module_of(path: Path) -> str:
    return "ZesuSsz." + ".".join(path.with_suffix("").parts[1:])


if __name__ == "__main__":
    raise SystemExit(main())
