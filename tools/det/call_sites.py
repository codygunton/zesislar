#!/usr/bin/env python3
"""The calls a segment makes, and the closed contract each one needs.

A block must never step into a callee: the `jal`/`jalr` targets inside a
segment's range are exactly the persistent `instr_pre` premises its
statement owes, and a generated segment carries one per distinct target.
Without them the automation walks into the callee and asks for an
instruction the index does not hold.

Targets come from the disassembly the build already produces; the
contract for each target is the closed B2/B4 spec, listed in
`ZesuSsz/Evidence/det/call_contracts.json`.
"""

from __future__ import annotations

import argparse
import json
import re
from pathlib import Path

DUMPS = Path("experiments/islaris-write-success/generated")
CONTRACTS = Path("ZesuSsz/Evidence/det/call_contracts.json")
CALL = re.compile(r"^\s*([0-9a-f]+):\s+[0-9a-f]+\s+(jal|jalr)\s+(.*)$")
COMMENTED = re.compile(r"#\s*([0-9a-f]+)\s*<([^>]*)>")
DIRECT = re.compile(r"(?:ra,)?\s*([0-9a-f]+)\s*<([^>]*)>")


def call_sites(dumps: Path = DUMPS) -> dict[int, tuple[int | None, str]]:
    found: dict[int, tuple[int | None, str]] = {}
    for dump in sorted(dumps.glob("block_*.dump")):
        for line in dump.read_text().split("\n"):
            match = CALL.match(line)
            if not match:
                continue
            rest = match.group(3)
            where = COMMENTED.search(rest) or DIRECT.match(rest.strip())
            found[int(match.group(1), 16)] = (
                (int(where.group(1), 16), where.group(2)) if where
                else (None, rest.strip()[:40]))
    return found


def contracts(path: Path = CONTRACTS) -> dict[int, dict]:
    data = json.loads(path.read_text())["contracts"]
    return {int(address, 16): entry for address, entry in data.items()}


def premises(entry: int, exit_address: int, dumps: Path = DUMPS,
             table: Path = CONTRACTS) -> tuple[list[str], list[str], list[int]]:
    """The `instr_pre` premises, the modules they need, and the unknowns."""
    known = contracts(table)
    targets, unknown = [], []
    for site, (target, _) in sorted(call_sites(dumps).items()):
        if not entry <= site < exit_address or target is None:
            continue
        if target in known and target not in targets:
            targets.append(target)
        elif target not in known and target not in unknown:
            unknown.append(target)
    lines = [f"  □ instr_pre {hex(target)} {known[target]['name']} -∗"
             for target in targets]
    modules = []
    for target in targets:
        module = known[target]["module"]
        if module not in modules:
            modules.append(module)
    return lines, modules, unknown


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--entry", required=True)
    parser.add_argument("--exit", dest="exit_address", required=True)
    arguments = parser.parse_args()
    lines, modules, unknown = premises(int(arguments.entry, 16),
                                       int(arguments.exit_address, 16))
    print("\n".join(lines) or "  (no call sites in range)")
    print("modules:", ", ".join(modules) or "none")
    if unknown:
        print("no closed contract for:", ", ".join(hex(a) for a in unknown))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
