#!/usr/bin/env python3
"""Generate an Islaris dump from a pinned objdump listing and a region profile."""

import argparse
import json
import re
from pathlib import Path

INSTRUCTION = re.compile(r"^\s*([0-9a-f]+):\s+[0-9a-f]+\s+(.+)$")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--disassembly", required=True)
    parser.add_argument("--profile", required=True)
    parser.add_argument("--output", required=True)
    args = parser.parse_args()

    profile = json.loads(Path(args.profile).read_text())
    ranges = [(int(a, 0), int(b, 0)) for a, b in profile["ranges"]]
    lines = [f'//@isla-config: {profile["islaConfig"]}']

    for line in Path(args.disassembly).read_text().splitlines():
        match = INSTRUCTION.match(line)
        if match is None:
            continue
        pc = int(match.group(1), 16)
        if not any(lower <= pc < upper for lower, upper in ranges):
            continue
        instruction = match.group(2)
        for base, constraints in profile.get("constraintsByMemoryBase", {}).items():
            if f"({base})" in instruction:
                lines.extend(f"//@constraint: {constraint}" for constraint in constraints)
        lines.append(line)

    Path(args.output).parent.mkdir(parents=True, exist_ok=True)
    Path(args.output).write_text("\n".join(lines) + "\n")


if __name__ == "__main__":
    main()
