#!/usr/bin/env python3
"""Size a build against coqc processes outside its worktree."""

from __future__ import annotations

import argparse
import os
import sys
from pathlib import Path


def compiler_pids(proc: Path) -> set[int]:
    result = set()
    for process in proc.iterdir():
        if not process.name.isdecimal():
            continue
        try:
            if (process / "comm").read_text().strip() != "coqc":
                continue
        except (OSError, UnicodeError):
            continue
        try:
            executable = (process / "exe").resolve(strict=True).name
        except OSError:
            executable = ""
        if executable not in {"bash", "sh", "dash", "zsh", "ksh"}:
            result.add(int(process.name))
    return result


def writer_pids(reservations: Path, proc: Path, compilers: set[int]) -> set[int]:
    result = set()
    for marker in reservations.glob("*"):
        try:
            owner = int(marker.name.split(".", 1)[0])
            os.kill(owner, 0)
            lines = marker.read_text().splitlines()
            if not any(line.startswith("writer=") and line[7:] for line in lines):
                continue
            child = int(lines[0]) if lines[0].isdecimal() else owner
            children = (proc / str(child) / "task" / str(child) / "children")
            candidates = {child}
            try:
                candidates.update(map(int, children.read_text().split()))
            except (OSError, ValueError):
                pass
            result.update(candidates & compilers)
        except (OSError, ValueError):
            continue
    return result


def owns_cwd(cwd: Path, root: Path, own_build_dir: Path | None = None) -> bool:
    nested_worktrees = root / ".worktrees"
    in_worktree = (cwd == root or root in cwd.parents) and not (
        cwd == nested_worktrees or nested_worktrees in cwd.parents
    )
    return in_worktree or (own_build_dir is not None and (
        cwd == own_build_dir or own_build_dir in cwd.parents
    ))


def counts(root: Path, proc: Path = Path("/proc"),
           pids: set[int] | None = None,
           own_build_dir: Path | None = None) -> tuple[int, int]:
    """Return (all coqc, coqc with a working directory under root)."""
    root = root.resolve()
    own_build_dir = own_build_dir.resolve() if own_build_dir is not None else None
    if pids is None:
        pids = compiler_pids(proc)
    total, own = len(pids), 0
    for pid in pids:
        process = proc / str(pid)
        try:
            cwd = (process / "cwd").resolve(strict=True)
            if owns_cwd(cwd, root, own_build_dir):
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
                      maximum: int = 48, fair_share: int = 32,
                      writers: int = 0, own_writers: int = 0,
                      writer_reserved: int = 0
                      ) -> tuple[int, int, int]:
    other = max(0, total - own)
    cap = min(maximum - other, fair_share if other else maximum)
    if writer_reserved:
        nonwriter_other = max(0, other - max(0, writers - own_writers))
        cap = min(cap, maximum - writer_reserved - nonwriter_other)
    return max(0, min(requested, cap)), own, other


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("root", type=Path)
    parser.add_argument("requested", type=int)
    parser.add_argument("--proc", type=Path, default=Path("/proc"))
    parser.add_argument("--drain-floor", type=int, default=None)
    parser.add_argument("--writer-reservations", type=Path, default=None)
    parser.add_argument("--own-build-dir", type=Path, default=None)
    arguments = parser.parse_args()
    maximum = int(os.environ.get("ZESU_MAX_COQC", "48"))
    fair_share = int(os.environ.get("ZESU_FAIR_SHARE_COQC", "32"))
    if arguments.requested < 1 or maximum < 1 or fair_share < 1:
        parser.error("requested width and coqc limits must be positive")
    snapshot = compiler_pids(arguments.proc)
    own_build_dir = (arguments.own_build_dir.resolve()
                     if arguments.own_build_dir is not None else None)
    total, own = counts(arguments.root, arguments.proc, snapshot, own_build_dir)
    writers = own_writers = 0
    if arguments.writer_reservations is not None:
        pids = writer_pids(arguments.writer_reservations, arguments.proc, snapshot)
        writers = len(pids)
        for pid in pids:
            try:
                cwd = (arguments.proc / str(pid) / "cwd").resolve(strict=True)
                root = arguments.root.resolve()
                if owns_cwd(cwd, root, own_build_dir):
                    own_writers += 1
            except OSError:
                pass
    nonwriters = total - writers
    if arguments.drain_floor is not None and nonwriters > arguments.drain_floor:
        print(f"drain incomplete: {nonwriters} coqc remain", file=sys.stderr)
        return 3
    slots, own, other = width_from_counts(arguments.requested, total, own,
                                          maximum, fair_share, writers, own_writers,
                                          16 if arguments.writer_reservations is not None else 0)
    print(f"{slots} {own} {other}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
