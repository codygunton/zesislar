#!/usr/bin/env python3
"""Size a build against coqc processes outside its worktree."""

from __future__ import annotations

import argparse
import os
import sys
from pathlib import Path


def counts(root: Path, proc: Path = Path("/proc")) -> tuple[int, int]:
    """Return (all coqc, coqc with a working directory under root)."""
    root = root.resolve()
    total = own = 0
    for process in proc.iterdir():
        if not process.name.isdecimal():
            continue
        try:
            if (process / "comm").read_text().strip() != "coqc":
                continue
            total += 1
        except (OSError, UnicodeError):
            continue
        try:
            cwd = (process / "cwd").resolve(strict=True)
            nested_worktrees = root / ".worktrees"
            if (cwd == root or root in cwd.parents) and not (
                cwd == nested_worktrees or nested_worktrees in cwd.parents
            ):
                own += 1
        except (OSError, UnicodeError):
            # An unreadable cwd remains in the other-agent count.
            continue
    return total, own


def width(requested: int, root: Path, proc: Path = Path("/proc"),
          maximum: int = 48, fair_share: int = 32) -> tuple[int, int, int]:
    total, own = counts(root, proc)
    return width_from_counts(requested, total, own, maximum, fair_share)


def width_from_counts(requested: int, total: int, own: int,
                      maximum: int = 48, fair_share: int = 32
                      ) -> tuple[int, int, int]:
    other = max(0, total - own)
    cap = min(maximum - other, fair_share if other else maximum)
    return max(0, min(requested, cap)), own, other


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("root", type=Path)
    parser.add_argument("requested", type=int)
    parser.add_argument("--proc", type=Path, default=Path("/proc"))
    parser.add_argument("--drain-floor", type=int, default=None)
    arguments = parser.parse_args()
    maximum = int(os.environ.get("ZESU_MAX_COQC", "48"))
    fair_share = int(os.environ.get("ZESU_FAIR_SHARE_COQC", "32"))
    if arguments.requested < 1 or maximum < 1 or fair_share < 1:
        parser.error("requested width and coqc limits must be positive")
    total, own = counts(arguments.root, arguments.proc)
    if arguments.drain_floor is not None and total > arguments.drain_floor:
        print(f"drain incomplete: {total} coqc remain", file=sys.stderr)
        return 3
    slots, own, other = width_from_counts(arguments.requested, total, own,
                                          maximum, fair_share)
    print(f"{slots} {own} {other}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
