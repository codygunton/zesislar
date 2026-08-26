"""Shared helpers for concrete Level 1 contract evidence checkers."""

from __future__ import annotations

import argparse
import json
from dataclasses import dataclass
from pathlib import Path
from typing import Callable


def one(rows: list, description: str):
    if len(rows) != 1:
        raise ValueError(f"expected one {description}, found {len(rows)}")
    return rows[0]


@dataclass(frozen=True)
class ContractRun:
    vector: dict
    observed: dict
    occurrence: dict


@dataclass(frozen=True)
class ContractContext:
    artifact: dict
    boundary: dict
    binding: dict
    runs: list[ContractRun]


def context(qualified: str, manifest: dict, bindings: dict, evidence: dict,
            require_every_vector: bool = False) -> ContractContext:
    if not (manifest["artifact"] == bindings["artifact"] == evidence["artifact"]):
        raise ValueError("contract evidence artifacts differ")
    boundary = one([row for row in manifest["instances"]
                    if row["qualified"] == qualified], f"{qualified} manifest boundary")
    binding = one([row for row in bindings["instances"]
                   if row["qualified"] == qualified], f"{qualified} binding")
    runs = []
    for vector in evidence["vectors"]:
        observed = one([row for row in vector["instances"]
                        if row["qualified"] == qualified],
                       f"{qualified} evidence row for {vector['label']}")
        if not observed["entryReached"]:
            if require_every_vector:
                raise ValueError(f"{qualified} entry absent from {vector['label']}")
            continue
        occurrence = one(observed["occurrences"],
                         f"{qualified} occurrence for {vector['label']}")
        runs.append(ContractRun(vector, observed, occurrence))
    if not runs:
        raise ValueError(f"no {qualified} contract runs were checked")
    return ContractContext(evidence["artifact"], boundary, binding, runs)


def complete_registers(snapshot: dict, description: str) -> list[int]:
    if snapshot is None or snapshot["available"] != 2 ** 32 - 1:
        raise ValueError(f"unavailable register in {description}")
    return snapshot["values"]


def check_pc_extent(run: ContractRun, execution_pcs: set[int], exit_pc: int,
                    exit_is_captured_instruction: bool = False,
                    require_exact_extent: bool = False) -> int:
    label = run.vector["label"]
    if run.occurrence["afterPc"] != exit_pc:
        raise ValueError(f"contract did not reach its exit PC for {label}")
    expected_extent = execution_pcs | ({exit_pc} if exit_is_captured_instruction else set())
    expected_count = len(execution_pcs) + (1 if exit_is_captured_instruction else 0)
    observed_extent = set(run.observed["executedExtentPcs"])
    if (require_exact_extent and observed_extent != expected_extent) or not observed_extent <= expected_extent:
        raise ValueError(f"contract executed PC set differs for {label}")
    observed_count = run.occurrence["executedInstructionCount"]
    if observed_count <= 0 or (require_exact_extent and observed_count != expected_count):
        raise ValueError(f"contract step count differs for {label}")
    return observed_count - (1 if exit_is_captured_instruction else 0)


def make_report(contract: str, artifact: dict, runs: list[dict]) -> dict:
    return {
        "schemaVersion": 1,
        "artifact": artifact,
        "contract": contract,
        "scope": "one concrete contract check per reached evidence vector",
        "runs": runs,
    }


def run_cli(validate: Callable[[dict, dict, dict, dict], dict]) -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--spec", required=True, type=Path)
    parser.add_argument("--manifest", required=True, type=Path)
    parser.add_argument("--bindings", required=True, type=Path)
    parser.add_argument("--evidence", required=True, type=Path)
    parser.add_argument("--output", required=True, type=Path)
    args = parser.parse_args()
    report = validate(*[json.loads(path.read_text()) for path in
                        (args.spec, args.manifest, args.bindings, args.evidence)])
    args.output.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n")
    return 0
