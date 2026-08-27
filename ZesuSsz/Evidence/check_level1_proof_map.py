#!/usr/bin/env python3
"""Validate claims in the Level 1 viewer payload."""

from __future__ import annotations

import argparse
import json
from pathlib import Path


def validate(proof_map: dict, manifest: dict, evidence: dict, bindings: dict) -> None:
    expected = {row["id"] for row in manifest["instances"]}
    boundaries = {row["instanceId"]: row for row in proof_map["boundaries"]}
    if set(boundaries) != expected or len(boundaries) != 6:
        raise ValueError("proof map does not contain the exact six Level 1 boundaries")
    if {row["id"] for row in bindings["instances"]} != expected:
        raise ValueError("binding inventory differs from the manifest")
    for vector in evidence["vectors"]:
        if {row["id"] for row in vector["instances"]} != expected:
            raise ValueError("evidence inventory differs from the manifest")
    for row in boundaries.values():
        if row["evidenceStatus"] != "captured":
            raise ValueError("a boundary does not report captured evidence")
        if row["contractStatus"] != "specified_assumption":
            raise ValueError("a boundary does not report the contract assumption")
        if row["proofStatus"] not in {"not_started", "proved"}:
            raise ValueError("a boundary has an unknown proof status")
        if row["proofStatus"] == "proved":
            if not row.get("theorem") or row.get("provedInstructionCount", 0) <= 0:
                raise ValueError("a proved boundary lacks its theorem or instruction count")
        elif row.get("provedInstructionCount", 0) != 0:
            raise ValueError("an unproved boundary reports proved instructions")
    statuses = {node.get("proofStatus") for node in proof_map["refinementGraph"]["nodes"]
                if node.get("proofStatus")}
    if not statuses <= {"not_started", "proved", "in_progress"}:
        raise ValueError("the refinement graph has an unknown proof status")
    proved_count = sum(row.get("provedInstructionCount", 0)
                       for row in boundaries.values())
    if proof_map["formalCoverage"]["directPcCount"] != proved_count:
        raise ValueError("formal coverage differs from proved instruction counts")
    if (proof_map["formalCoverage"]["boundaryRegionPcCount"] >
            proof_map["formalCoverage"]["endpointPcCount"]):
        raise ValueError("boundary coverage exceeds the endpoint instruction count")


def main() -> int:
    parser = argparse.ArgumentParser()
    for name in ("proof-map", "manifest", "evidence", "bindings"):
        parser.add_argument("--" + name, required=True, type=Path)
    args = parser.parse_args()
    validate(*[json.loads(getattr(args, name.replace("-", "_")).read_text())
               for name in ("proof-map", "manifest", "evidence", "bindings")])
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
