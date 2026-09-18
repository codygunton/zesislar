"""Read the proofs of a Rocq module without a Rocq process.

The residual corpus needs two facts about every hand-written proof: the text
that states it, and the hand lines that close it. Both come from the module
text, so this parser stays deliberately shallow: it finds the declaration
line, its `Proof.`, and its terminator, and it tracks the `Section` and
`Module` blocks that a probe must close again.
"""

from __future__ import annotations

import re
from dataclasses import dataclass, field
from pathlib import Path

DECLARATION = re.compile(
    r"^(?P<kind>Lemma|Theorem|Corollary|Fact|Remark|Example|Definition|Instance"
    r"|Global Instance|Local Lemma|Local Instance|Program Definition)\s+"
    r"(?P<name>[A-Za-z_][A-Za-z0-9_']*)")
PROOF_OPENER = re.compile(r"^\s*Proof(\s+using\b[^.]*)?\.(?P<rest>.*)$")
TERMINATOR = re.compile(
    r"^(?P<body>.*?)\s*\b(?P<kind>Qed|Defined|Admitted|Abort)\s*\.\s*$")
SECTION_OPEN = re.compile(r"^\s*Section\s+(?P<name>[A-Za-z_][A-Za-z0-9_']*)\s*\.")
MODULE_OPEN = re.compile(
    r"^\s*Module\s+(?!Type\b|Import\b)(?P<name>[A-Za-z_][A-Za-z0-9_']*)"
    r"(?![^.]*:=)[^.]*\.\s*$")
BLOCK_CLOSE = re.compile(r"^\s*End\s+(?P<name>[A-Za-z_][A-Za-z0-9_']*)\s*\.")


@dataclass
class Proof:
    """One `Proof. ... Qed.` and the declaration it closes."""

    module: str
    name: str
    kind: str
    declaration_line: int  # 0-based index of the declaration line
    proof_line: int        # 0-based index of the `Proof.` line
    terminator_line: int   # 0-based index of `Qed.`, or the `Proof.` line itself
    inline: bool           # the whole proof sits on the `Proof.` line
    body: list[str] = field(default_factory=list)
    open_blocks: list[str] = field(default_factory=list)

    @property
    def hand_lines(self) -> list[str]:
        """The body lines with the block automation call removed."""
        return [line for line in (raw.strip() for raw in self.body)
                if line and not is_automation_line(line)]

    @property
    def automation_only(self) -> bool:
        return not self.hand_lines


AUTOMATION_LINES = {
    "zesu_block.", "zesu_block", "zesu_block_simpl.", "zesu_block_simpl",
    "Proof.", "Qed.",
}


def is_automation_line(line: str) -> bool:
    return line in AUTOMATION_LINES


def parse_module(path: Path) -> list[Proof]:
    """Return every proof of `path`, in source order."""
    lines = path.read_text().split("\n")
    module = path.name
    proofs: list[Proof] = []
    blocks: list[str] = []
    declaration: tuple[int, str, str] | None = None
    index = 0
    while index < len(lines):
        line = lines[index]
        opener = SECTION_OPEN.match(line) or MODULE_OPEN.match(line)
        if opener:
            blocks.append(opener.group("name"))
            index += 1
            continue
        closer = BLOCK_CLOSE.match(line)
        if closer and blocks and blocks[-1] == closer.group("name"):
            blocks.pop()
            index += 1
            continue
        found = DECLARATION.match(line)
        if found:
            declaration = (index, found.group("kind"), found.group("name"))
            index += 1
            continue
        proof = PROOF_OPENER.match(line)
        if proof is None or declaration is None:
            index += 1
            continue
        rest = proof.group("rest").strip()
        if rest:
            closing = TERMINATOR.match(rest)
            if closing:
                rest = closing.group("body").strip()
            proofs.append(Proof(
                module=module, name=declaration[2], kind=declaration[1],
                declaration_line=declaration[0], proof_line=index,
                terminator_line=index, inline=True,
                body=[rest] if rest else [], open_blocks=list(blocks)))
            index += 1
            continue
        end = index + 1
        closing = None
        while end < len(lines):
            closing = TERMINATOR.match(lines[end])
            if closing:
                break
            end += 1
        body = lines[index + 1:min(end, len(lines))]
        if closing and closing.group("body").strip():
            body = body + [closing.group("body")]
        proofs.append(Proof(
            module=module, name=declaration[2], kind=declaration[1],
            declaration_line=declaration[0], proof_line=index,
            terminator_line=min(end, len(lines) - 1), inline=False,
            body=body, open_blocks=list(blocks)))
        index = end + 1
    return proofs


def find_proof(path: Path, lemma: str) -> Proof:
    for proof in parse_module(path):
        if proof.name == lemma:
            return proof
    raise KeyError(f"{path.name} states no proof named {lemma}")
