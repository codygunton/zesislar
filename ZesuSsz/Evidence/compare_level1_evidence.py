#!/usr/bin/env python3
"""Compare Level 1 reports after normalizing the QEMU user-stack base."""

from __future__ import annotations

import argparse
import json
from pathlib import Path


STACK_LOWER = 0x7FFF00000000
STACK_UPPER = 0x800000000000


def normalize(report: dict) -> dict:
    successful = [row for row in report["sszDecodeObservedRuns"]
                  if row["outcome"] == "success"]
    if len(successful) != 1:
        raise ValueError("expected one successful decoder run")
    base = successful[0]["successResultAddress"]
    if not STACK_LOWER <= base < STACK_UPPER:
        raise ValueError("the success result is outside the QEMU user stack")

    def visit(value):
        if isinstance(value, dict):
            return {key: visit(item) for key, item in value.items()}
        if isinstance(value, list):
            return [visit(item) for item in value]
        if isinstance(value, int) and STACK_LOWER <= value < STACK_UPPER:
            return value - base
        return value

    return visit(report)


def compare(left: dict, right: dict) -> None:
    if normalize(left) != normalize(right):
        raise ValueError("normalized Level 1 evidence differs")


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("left", type=Path)
    parser.add_argument("right", type=Path)
    args = parser.parse_args()
    compare(json.loads(args.left.read_text()), json.loads(args.right.read_text()))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
