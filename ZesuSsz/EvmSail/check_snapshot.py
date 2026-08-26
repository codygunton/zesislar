#!/usr/bin/env python3
"""Check the pinned EVM-Sail Rocq snapshot and its supported local adaptations."""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--snapshot", type=Path, default=Path("generated/evm-sail-coq"))
    parser.add_argument("--generated", type=Path)
    args = parser.parse_args()
    manifest = json.loads((args.snapshot / "SOURCE.json").read_text())
    for name, expected in manifest["snapshotSha256"].items():
        actual = digest(args.snapshot / name)
        if actual != expected:
            raise ValueError(f"snapshot digest differs for {name}: {actual}")
    if args.generated is not None:
        for name in ("evm_decoder.v", "evm_decoder_types.v"):
            source = args.generated / name
            if source.read_bytes() != (args.snapshot / name).read_bytes():
                raise ValueError(f"generated source differs for {name}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
