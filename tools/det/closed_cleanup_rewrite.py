#!/usr/bin/env python3
"""Replace one listed proof body, without changing its statement or neighbors.

The default is a dry run. Compile and compare Print Assumptions before and
after each replacement; this tool does not claim that the new proof closes.
"""

from __future__ import annotations

import argparse
import hashlib
import re
import subprocess
from pathlib import Path


PROOF = "Proof. move => *. zesu_block. Qed."
DECLARATION = re.compile(
    r"(?m)^(?:Local |Global )?(?:Lemma|Theorem|Corollary|Fact|Proposition)\s+"
)
PROOF_START = re.compile(r"(?m)^Proof(?:\s+using\s+[^.]*)?\.")
PROOF_END = re.compile(r"\b(?:Qed|Defined|Admitted|Abort)\.")


def listed_rows(path: Path) -> dict[tuple[str, str], tuple[int, float]]:
    rows: dict[tuple[str, str], tuple[int, float]] = {}
    for number, line in enumerate(path.read_text().splitlines(), 1):
        if not line or line.startswith("#"):
            continue
        fields = line.split()
        if len(fields) != 4:
            raise ValueError(f"{path}:{number}: expected four fields")
        module, lemma, hand_lines, seconds = fields
        key = module, lemma
        if key in rows:
            raise ValueError(f"{path}:{number}: duplicate {module} {lemma}")
        rows[key] = int(hand_lines), float(seconds)
    return rows


def proof_span(source: str, lemma: str) -> tuple[int, int]:
    declarations = [
        match for match in DECLARATION.finditer(source)
        if re.match(rf"{re.escape(lemma)}\b", source[match.end():])
    ]
    if len(declarations) != 1:
        raise ValueError(f"expected one declaration for {lemma}; found {len(declarations)}")
    declaration = declarations[0]
    next_declaration = DECLARATION.search(source, declaration.end())
    limit = next_declaration.start() if next_declaration else len(source)
    start = PROOF_START.search(source, declaration.end(), limit)
    if start is None:
        raise ValueError(f"{lemma}: no Proof command before the next declaration")
    end = PROOF_END.search(source, start.end(), limit)
    if end is None or end.group() != "Qed.":
        raise ValueError(f"{lemma}: proof does not end with Qed")
    if PROOF_START.search(source, start.end(), end.start()):
        raise ValueError(f"{lemma}: nested Proof command")
    return start.start(), end.end()


def clean_path(path: Path) -> bool:
    result = subprocess.run(
        ["git", "status", "--porcelain", "--", str(path)],
        check=True, capture_output=True, text=True,
    )
    return not result.stdout.strip()


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--list", type=Path, required=True)
    parser.add_argument("--module", required=True, help="exact .v basename")
    parser.add_argument("--lemma", action="append",
                        help="named lemma; omit to select every listed lemma in the module")
    parser.add_argument("--apply", action="store_true")
    args = parser.parse_args()

    rows = listed_rows(args.list)
    names = args.lemma or [lemma for module, lemma in rows if module == args.module]
    if not names or len(names) != len(set(names)):
        parser.error("no listed lemmas or duplicate --lemma")
    for lemma in names:
        if (args.module, lemma) not in rows:
            parser.error(f"not listed: {args.module} {lemma}")
    paths = list(Path("ZesuSsz/Proofs").rglob(args.module))
    if len(paths) != 1:
        parser.error(f"expected one module path; found {len(paths)}")
    path = paths[0]
    source = path.read_text()
    edits: list[tuple[int, int, str]] = []
    for lemma in names:
        start, end = proof_span(source, lemma)
        before = source[start:end]
        digest = hashlib.sha256(before.encode()).hexdigest()[:16]
        hand_lines, seconds = rows[args.module, lemma]
        print(f"{path} {lemma}: listed_lines={hand_lines} "
              f"probe_seconds={seconds:.1f} old_proof_sha256={digest}")
        if before != PROOF:
            edits.append((start, end, lemma))
    if not edits:
        print("already replaced")
        return 0
    if args.apply:
        if not clean_path(path):
            parser.error(f"refuse modified file: {path}")
        for start, end, lemma in sorted(edits, reverse=True):
            source = source[:start] + PROOF + source[end:]
        path.write_text(source)
        print(f"applied {len(edits)} proofs; compile and compare Print Assumptions before commit")
    else:
        print(f"dry run: {len(edits)} proofs; add --apply to replace")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
