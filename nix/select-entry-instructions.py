#!/usr/bin/env python3
"""Select the six Level 1 entry instructions from an LLVM disassembly."""

import argparse
import re
from pathlib import Path


LINE = re.compile(
    r"^\s*([0-9a-fA-F]+):\s+([0-9a-fA-F]{8}|(?:[0-9a-fA-F]{2}\s+){3}[0-9a-fA-F]{2})\s+(.+)$"
)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--disassembly", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("pcs", nargs="+")
    args = parser.parse_args()

    wanted = {int(pc, 16): pc.lower() for pc in args.pcs}
    selected: dict[int, tuple[str, str]] = {}
    for line in args.disassembly.read_text().splitlines():
        match = LINE.match(line)
        if match is None:
            continue
        pc = int(match.group(1), 16)
        if pc not in wanted:
            continue
        encoded = match.group(2).split()
        opcode = encoded[0] if len(encoded) == 1 else "".join(reversed(encoded))
        selected[pc] = (opcode, match.group(3).strip())

    missing = sorted(set(wanted) - set(selected))
    if missing:
        raise SystemExit("missing entry PCs: " + ", ".join(hex(pc) for pc in missing))

    rows = [
        "//@isla-config: riscv64_zesu.toml",
        "//@constraint: = ((_ extract 2 2) misa.bits) 0b0",
    ]
    for pc in wanted:
        opcode, instruction = selected[pc]
        rows.append(f"   {pc:x}:\t{opcode}          \t{instruction}")
    args.output.write_text("\n".join(rows) + "\n")


if __name__ == "__main__":
    main()
