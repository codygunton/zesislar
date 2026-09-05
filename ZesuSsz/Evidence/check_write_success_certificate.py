#!/usr/bin/env python3
"""Check that a writeSuccess CFG certificate matches its pinned CFG."""

from __future__ import annotations

import argparse
import json
from pathlib import Path

from generate_write_success_certificate import generate


def validate(certificate: dict, cfg: dict, *, elf: Path | None = None,
             expected_sha256: str | None = None) -> None:
    budgets = None
    if "loopBudgets" in certificate:
        budgets = {
            (int(row["from"]), int(row["to"])): int(row["maxTraversals"])
            for row in certificate["loopBudgets"]
        }
    expected = generate(cfg, elf=elf, expected_sha256=expected_sha256,
                        loop_budgets=budgets)
    if certificate != expected:
        raise ValueError("writeSuccess CFG certificate does not match the pinned CFG")


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--certificate", required=True, type=Path)
    parser.add_argument("--cfg", required=True, type=Path)
    parser.add_argument("--elf", type=Path)
    parser.add_argument("--expected-sha256")
    args = parser.parse_args()
    validate(json.loads(args.certificate.read_text()),
             json.loads(args.cfg.read_text()), elf=args.elf,
             expected_sha256=args.expected_sha256)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
