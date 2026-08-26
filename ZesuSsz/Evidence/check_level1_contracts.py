#!/usr/bin/env python3
"""Check the fixed six-contract boundary for the pinned endpoint."""

from __future__ import annotations

import json
import sys
from pathlib import Path


EXPECTED = {
    "read_input": 0x10140,
    "zkvm_exit": 0x101C4,
    "ssz_decode_root.decodeInput": 0x12168,
    "alt_fl_alloc.get": 0x14CCC,
    "ssz_decode_observation.writeSuccess": 0x14D30,
    "ssz_decode_observation.writeFailure": 0x161C0,
}


def validate(manifest: dict) -> None:
    actual = {row["qualified"]: row["entryPc"] for row in manifest["instances"]}
    if actual != EXPECTED:
        raise ValueError(f"Level 1 contract boundary differs: {actual}")


def main() -> int:
    validate(json.loads(Path(sys.argv[1]).read_text()))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
