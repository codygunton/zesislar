#!/usr/bin/env python3
"""Check the observable zkvm_exit contract clauses for concrete QEMU runs."""

from __future__ import annotations

import argparse
import json
from pathlib import Path


def _one(rows: list[dict], description: str) -> dict:
    if len(rows) != 1:
        raise ValueError(f"expected one {description}, found {len(rows)}")
    return rows[0]


def validate(spec: dict, manifest: dict, bindings: dict, evidence: dict) -> dict:
    if spec.get("contract") != "zkvm_exit":
        raise ValueError("unexpected contract evidence specification")
    if not (manifest["artifact"] == bindings["artifact"] == evidence["artifact"]):
        raise ValueError("contract evidence artifacts differ")

    boundary = _one([row for row in manifest["instances"]
                     if row["qualified"] == "zkvm_exit"], "zkvm_exit manifest boundary")
    binding = _one([row for row in bindings["instances"]
                    if row["qualified"] == "zkvm_exit"], "zkvm_exit binding")
    code_binding = _one([row for row in binding["bindings"] if row["name"] == "code"],
                        "zkvm_exit code binding")
    code_register = spec["argumentRegister"]
    if code_binding.get("machineRegister") != code_register:
        raise ValueError("zkvm_exit code register differs from the contract specification")

    terminal_pc = _one(boundary["exitPcs"], "zkvm_exit terminal PC")
    execution_pcs = set(boundary["executionPcs"]) - {terminal_pc}
    exit_code_address = spec["ioContextAddress"] + spec["exitCodeOffset"]
    reports = []
    for vector in evidence["vectors"]:
        observed = _one([row for row in vector["instances"]
                         if row["qualified"] == "zkvm_exit"],
                        f"zkvm_exit evidence row for {vector['label']}")
        occurrence = _one(observed["occurrences"],
                          f"zkvm_exit occurrence for {vector['label']}")
        entry = occurrence["entryRegisters"]
        if entry["available"] != 2 ** 32 - 1:
            raise ValueError(f"unavailable zkvm_exit entry register for {vector['label']}")
        code = entry["values"][code_register]
        if not 0 <= code < 2 ** 64:
            raise ValueError(f"zkvm_exit code is outside UInt64 for {vector['label']}")
        if occurrence["afterPc"] != terminal_pc:
            raise ValueError(f"zkvm_exit did not reach its terminal PC for {vector['label']}")
        if occurrence["executedInstructionCount"] != len(execution_pcs) + 1:
            raise ValueError(f"zkvm_exit step count differs for {vector['label']}")
        if set(observed["executedExtentPcs"]) != execution_pcs | {terminal_pc}:
            raise ValueError(f"zkvm_exit executed PC set differs for {vector['label']}")

        writes = occurrence["memoryWrites"]
        if len(writes) != 1:
            raise ValueError(f"zkvm_exit memory frame differs for {vector['label']}")
        write = writes[0]
        if ({key: write[key] for key in ("kind", "address", "width", "value")} != {
                "kind": "store", "address": exit_code_address, "width": 8, "value": code
            } or write["pc"] not in execution_pcs):
            raise ValueError(f"zkvm_exit memory frame differs for {vector['label']}")
        if occurrence["hostWrites"]:
            raise ValueError(f"zkvm_exit changed stdout for {vector['label']}")

        terminal = _one(vector["terminalOutputs"],
                        f"terminal output for {vector['label']}")
        prior_outputs = {(write["address"], write["bytes"])
                         for row in vector["instances"]
                         for write in row["hostWrites"]}
        if (terminal["address"], terminal["bytes"]) not in prior_outputs:
            raise ValueError(f"zkvm_exit terminal stdout differs for {vector['label']}")

        reports.append({
            "vector": vector["label"],
            "verdict": "observable clauses passed",
            "code": code,
            "entryPc": boundary["entryPc"],
            "terminalPc": terminal_pc,
            "observedStepCount": len(execution_pcs),
            "exitCodeStoreAddress": exit_code_address,
            "passedClauses": spec["observableClauses"],
            "unmeasuredClauses": spec["unobservableClauses"],
        })
    if not reports:
        raise ValueError("no zkvm_exit contract runs were checked")
    return {
        "schemaVersion": 1,
        "artifact": evidence["artifact"],
        "contract": "zkvm_exit",
        "scope": "one concrete contract check per evidence vector",
        "runs": reports,
    }


def main() -> int:
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


if __name__ == "__main__":
    raise SystemExit(main())
