"""Read the parts of a printed Rocq goal.

`Show` prints a Coq context above a rule of `=` characters, and the Iris
proof mode prints its own hypotheses above a rule of `-` characters that ends
in `∗` or `□`. A residual goal often carries both, so the conclusion is what
follows the LAST rule of either kind.
"""

from __future__ import annotations

import re

IRIS_RULE = re.compile(r"^-{3,}[∗□_*]?$")
COQ_RULE = re.compile(r"^={3,}$")
GOAL_SEPARATOR = re.compile(r"^goal \d+ is:$")
HEAD_NAME = re.compile(r"([A-Za-z_][A-Za-z0-9_.']*)")
HEAD_OPENERS = re.compile(r"^[⌜\"'(\[⎡]+")
HEAD_LIMIT = 200
HEAD_NAME_LIMIT = 48


def is_rule(line: str) -> bool:
    stripped = line.strip()
    return bool(IRIS_RULE.match(stripped) or COQ_RULE.match(stripped))


def split_goals(goal_text: str) -> list[str]:
    """One block per goal that `Show` printed."""
    blocks: list[list[str]] = [[]]
    for line in goal_text.split("\n"):
        if GOAL_SEPARATOR.match(line.strip()):
            blocks.append([])
            continue
        blocks[-1].append(line)
    return ["\n".join(block) for block in blocks if any(block)]


def split_goal(block: str) -> tuple[str, str]:
    """The context and the conclusion of one goal block."""
    lines = block.split("\n")
    rule = max((index for index, line in enumerate(lines) if is_rule(line)),
               default=None)
    if rule is None:
        return "", block.strip()
    return "\n".join(lines[:rule]), "\n".join(lines[rule + 1:]).strip()


def conclusion(block: str) -> str:
    """The first line of the conclusion of one goal block."""
    for line in split_goal(block)[1].split("\n"):
        if line.strip():
            return line.strip()[:HEAD_LIMIT]
    return ""


def head_constant(text: str) -> str:
    """The applied head of a conclusion, as a bare name where there is one.

    A conclusion that starts with a binder or a notation has no name, so the
    head is its first characters on one line. That keeps the head usable as a
    table key.
    """
    stripped = HEAD_OPENERS.sub("", text.strip())
    found = HEAD_NAME.match(stripped)
    if found:
        return found.group(1)
    return " ".join(stripped.split())[:HEAD_NAME_LIMIT]
