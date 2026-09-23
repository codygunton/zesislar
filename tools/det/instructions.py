#!/usr/bin/env python3
"""Instruction count of a lemma's block, from the registered trace addresses.

Every instruction of the write-success region is registered as one module
`a<hex>.v` under `generated/isla-traces/write_success_*`, on a stride of four
bytes. So the instructions a lemma covers are the registered addresses from
its entry (`instr_body 0x...`) up to its exit (the largest address the
statement names, or the end of the entry's block).
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "residual"))

from modules import find_proof  # noqa: E402

TRACES = Path("generated/isla-traces")
PROOF_DIR = Path("ZesuSsz/Proofs/WriteSuccess")
ADDRESS = re.compile(r"a([0-9a-f]{4,8})")
HEX_IN_TEXT = re.compile(r"0x([0-9a-fA-F]{4,8})")
ENTRY = re.compile(r"instr_body\s+0x([0-9a-fA-F]+)")


def registered(traces: Path = TRACES) -> list[int]:
    found: set[int] = set()
    for directory in traces.glob("write_success_*"):
        if not directory.is_dir():
            continue
        for module in directory.glob("a*.v"):
            match = ADDRESS.fullmatch(module.stem.replace("_spec", ""))
            if match:
                found.add(int(match.group(1), 16))
    return sorted(found)


def statement(module: Path, lemma: str) -> str:
    proof = find_proof(module, lemma)
    lines = module.read_text().split("\n")
    return "\n".join(lines[proof.declaration_line:proof.proof_line])


def count(module: Path, lemma: str, addresses: list[int]) -> dict:
    text = statement(module, lemma)
    named = sorted({int(value, 16) for value in HEX_IN_TEXT.findall(text)}
                   & set(addresses))
    entry = ENTRY.search(text)
    start = int(entry.group(1), 16) if entry else (named[0] if named else 0)
    end = named[-1] if named else start
    covered = [a for a in addresses if start <= a <= end]
    return {"module": module.name, "lemma": lemma,
            "entry": hex(start) if start else "",
            "exit": hex(end) if end else "",
            "addresses_named": [hex(a) for a in named],
            "instructions": max(1, len(covered))}


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--set", type=Path, required=True)
    parser.add_argument("--traces", type=Path, default=TRACES)
    parser.add_argument("--out", type=Path, default=None)
    arguments = parser.parse_args()
    addresses = registered(arguments.traces)
    rows = []
    for line in arguments.set.read_text().split("\n"):
        if ":" not in line:
            continue
        name, lemma = line.split(":", 1)
        path = Path(name)
        if not path.exists():
            path = PROOF_DIR / path.name
        if not path.exists():
            continue
        try:
            rows.append(count(path, lemma, addresses))
        except KeyError:
            continue
    if arguments.out:
        arguments.out.write_text("".join(json.dumps(r) + "\n" for r in rows))
    for row in rows:
        print(f"{row['instructions']:4d}  {row['entry']:>9s} -> "
              f"{row['exit']:<9s} {row['module']}:{row['lemma']}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
