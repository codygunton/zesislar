#!/usr/bin/env python3
"""Check the reviewed Level 1 evidence parity boundary."""

from __future__ import annotations

import hashlib
import json
import os
from pathlib import Path


ROOT = Path(os.environ.get("ZESU_SSZ_ROOT", Path(__file__).resolve().parents[2]))
REGISTRY = ROOT / "contracts" / "level1-evidence-parity.json"


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def validate() -> None:
    registry = json.loads(REGISTRY.read_text())
    evidence = ROOT / "ZesuSsz" / "Evidence"
    mismatches = []
    for name, expected in registry["exactFiles"].items():
        actual = sha256(evidence / name)
        if actual != expected:
            mismatches.append(f"{name}: expected {expected}, got {actual}")
    if mismatches:
        raise ValueError("Level 1 evidence parity failed:\n" + "\n".join(mismatches))

    adaptations = registry["rocqAdaptations"]
    for key in ("generator", "tests"):
        if not (evidence / adaptations[key]).is_file():
            raise ValueError(f"missing Rocq adaptation: {adaptations[key]}")
    if not (ROOT / adaptations["snapshot"]).is_file():
        raise ValueError(f"missing Rocq boundary snapshot: {adaptations['snapshot']}")

    contract = (ROOT / "ZesuSsz" / "Contracts" / "Endpoints.v").read_text()
    if "Require Import ZesuSsz.Generated.Level1." not in contract:
        raise ValueError("Level 1 contracts do not import the generated boundary map")
    forbidden = ("readInputRegion :", "decodeRegion :", "writeSuccessRegion :")
    if any(text in contract for text in forbidden):
        raise ValueError("Level 1 execution regions remain caller-selected")


if __name__ == "__main__":
    validate()
