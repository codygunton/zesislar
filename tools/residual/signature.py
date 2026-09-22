"""A normalized signature for a residual conclusion.

A rule author cannot act on "C1 with iIntros". They can act on
"∃ : spec  with  ⌜scons ⊆ scons_snap⌝", because that names a goal shape.
The signature is the head of the conclusion plus the shapes of its first
two arguments, with addresses, numbers and register names replaced by
placeholders, so the same shape at two addresses is one row.
"""

from __future__ import annotations

import re
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

from goals import head_constant  # noqa: E402

OPENERS = "([{⌜⎡"
CLOSERS = ")]}⌝⎤"
NUMBER = re.compile(r"\b0x[0-9a-fA-F]+\b|\b\d+\b")
REGISTER = re.compile(r'"[A-Za-z]+\d*"')
EXISTENTIAL = re.compile(r"^\s*(?:∃|exists)\s+(?P<binder>[^,]{0,200}),")
FIND = re.compile(r"find_in_context\s*\(\s*(?P<kind>Find\w+)")
ARROWS = ("↦ₘ∗", "↦ₘ?", "↦ₘ", "↦ᵣ", "-∗", "={⊤}=∗")
WIDTH = 72


def top_level_split(text: str, token: str) -> list[str]:
    """Split on `token` outside every bracket."""
    parts: list[str] = []
    depth = 0
    start = 0
    index = 0
    while index < len(text):
        if text.startswith("↦ₘ∗", index):
            index += 3
            continue
        character = text[index]
        if character in OPENERS:
            depth += 1
        elif character in CLOSERS:
            depth = max(0, depth - 1)
        elif depth == 0 and text.startswith(token, index):
            parts.append(text[start:index])
            index += len(token)
            start = index
            continue
        index += 1
    parts.append(text[start:])
    return [part.strip() for part in parts if part.strip()]


def placeholder(term: str) -> str:
    """One argument, reduced to its shape."""
    term = " ".join(term.split())
    for arrow in ARROWS:
        if arrow in term:
            return arrow
    if not term:
        return "_"
    if term[0] in OPENERS:
        return "(…)"
    if NUMBER.fullmatch(term):
        return "N"
    if REGISTER.fullmatch(term):
        return '"r"'
    head = head_constant(term)
    return head if head and head[0].isalpha() else "_"


def arguments(text: str) -> list[str]:
    """The top-level arguments of an application, in order."""
    parts: list[str] = []
    depth = 0
    current: list[str] = []
    for character in text:
        if character in OPENERS:
            depth += 1
        elif character in CLOSERS:
            depth = max(0, depth - 1)
        if depth == 0 and character.isspace():
            if current:
                parts.append("".join(current))
                current = []
            continue
        current.append(character)
    if current:
        parts.append("".join(current))
    return parts


def signature(conclusion: str) -> str:
    """The normalized shape of a conclusion."""
    text = " ".join(conclusion.split())
    if not text:
        return "(empty)"

    found = EXISTENTIAL.match(text)
    if found:
        binder = " ".join(found.group("binder").split())
        kind = binder.split(":", 1)[-1].strip() if ":" in binder else binder
        return f"∃ : {NUMBER.sub('N', kind)[:40]}"

    found = FIND.search(text)
    if found:
        return f"find_in_context({found.group('kind')})"

    conjuncts = top_level_split(text, "∗")
    if len(conjuncts) > 1:
        shapes = [placeholder(part) for part in conjuncts[:3]]
        more = "…" if len(conjuncts) > 3 else ""
        return f"∗[{len(conjuncts)}] " + " ∗ ".join(shapes) + more

    wand = top_level_split(text, "-∗")
    if len(wand) > 1:
        return f"{placeholder(wand[0])} -∗ {placeholder(wand[1])}"

    equation = top_level_split(text, " = ")
    if len(equation) > 1:
        return f"{placeholder(equation[0])} = {placeholder(equation[1])}"

    parts = arguments(text)
    head = head_constant(parts[0]) if parts else "_"
    shapes = [placeholder(part) for part in parts[1:3]]
    return (head + (" " + " ".join(shapes) if shapes else ""))[:WIDTH]
