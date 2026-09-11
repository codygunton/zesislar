#!/usr/bin/env python3
"""Add the shared automation import to every proof module."""

from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
IMPORT = "Require Import ZesuSsz.Automation.All.\n"


def main() -> None:
    changed = 0
    for path in sorted((ROOT / "ZesuSsz" / "Proofs").rglob("*.v")):
        text = path.read_text()
        if IMPORT.strip() in text:
            continue
        path.write_text(IMPORT + text)
        changed += 1
    print(f"updated {changed} proof modules")


if __name__ == "__main__":
    main()
