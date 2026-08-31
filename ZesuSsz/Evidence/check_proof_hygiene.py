#!/usr/bin/env python3
"""Reject proof placeholders and tracked generated Isla traces."""

import re
import subprocess
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
PLACEHOLDER = re.compile(
    r"^\s*(?:(?:Admitted|admit|Abort)\s*\.|Axiom\b)"
)


def tracked_files() -> list[str]:
    output = subprocess.check_output(
        ["git", "ls-files"], cwd=ROOT, text=True
    )
    return output.splitlines()


def main() -> None:
    failures: list[str] = []
    for name in tracked_files():
        if name.startswith("generated/isla-traces/"):
            failures.append(f"tracked generated Isla trace: {name}")
        if not name.startswith("ZesuSsz/Experiments/") or not name.endswith(".v"):
            continue
        for number, line in enumerate((ROOT / name).read_text().splitlines(), 1):
            if PLACEHOLDER.search(line):
                failures.append(f"proof placeholder: {name}:{number}: {line.strip()}")
    if failures:
        raise SystemExit("\n".join(failures))


if __name__ == "__main__":
    main()
