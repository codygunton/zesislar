#!/usr/bin/env python3
"""Keep the tracked corpus compressed.

The plain `corpus.jsonl` is 11 MiB and changes on every run, so the branch
tracks `corpus.jsonl.gz` instead. `--unpack` restores the plain file.
"""

from __future__ import annotations

import argparse
import gzip
import shutil
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

import corpus  # noqa: E402


def pack(plain: Path) -> Path:
    """Compress with a fixed timestamp, so an unchanged corpus is no diff."""
    packed = plain.with_suffix(plain.suffix + ".gz")
    with plain.open("rb") as source, packed.open("wb") as raw:
        with gzip.GzipFile(fileobj=raw, mode="wb", mtime=0) as target:
            shutil.copyfileobj(source, target)
    return packed


def unpack(packed: Path) -> Path:
    plain = packed.with_suffix("")
    with gzip.open(packed, "rb") as source, plain.open("wb") as target:
        shutil.copyfileobj(source, target)
    return plain


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--corpus", type=Path, default=corpus.CORPUS)
    parser.add_argument("--unpack", action="store_true")
    arguments = parser.parse_args()
    if arguments.unpack:
        packed = arguments.corpus.with_suffix(arguments.corpus.suffix + ".gz")
        print(f"{unpack(packed)} restored")
        return 0
    packed = pack(arguments.corpus)
    print(f"{packed} {packed.stat().st_size // 1024} KiB "
          f"from {arguments.corpus.stat().st_size // 1024} KiB")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
