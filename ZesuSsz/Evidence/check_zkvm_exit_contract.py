#!/usr/bin/env python3
"""Check the observable zkvm_exit contract clauses for concrete QEMU runs."""

from __future__ import annotations

from contract_evidence import (check_pc_extent, complete_registers, context,
                               make_report, one, run_cli)


def validate(spec: dict, manifest: dict, bindings: dict, evidence: dict) -> dict:
    if spec.get("contract") != "zkvm_exit":
        raise ValueError("unexpected contract evidence specification")
    checked = context("zkvm_exit", manifest, bindings, evidence, require_every_vector=True)
    boundary = checked.boundary
    code_binding = one([row for row in checked.binding["bindings"] if row["name"] == "code"],
                       "zkvm_exit code binding")
    code_register = spec["argumentRegister"]
    if code_binding.get("machineRegister") != code_register:
        raise ValueError("zkvm_exit code register differs from the contract specification")

    terminal_pc = one(boundary["exitPcs"], "zkvm_exit terminal PC")
    execution_pcs = set(boundary["executionPcs"]) - {terminal_pc}
    exit_code_address = spec["ioContextAddress"] + spec["exitCodeOffset"]
    reports = []
    for run in checked.runs:
        vector, occurrence = run.vector, run.occurrence
        entry = complete_registers(occurrence["entryRegisters"],
                                   f"zkvm_exit entry for {vector['label']}")
        code = entry[code_register]
        if not 0 <= code < 2 ** 64:
            raise ValueError(f"zkvm_exit code is outside UInt64 for {vector['label']}")
        step_count = check_pc_extent(run, execution_pcs, terminal_pc, True, True)

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

        terminal = one(vector["terminalOutputs"], f"terminal output for {vector['label']}")
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
            "observedStepCount": step_count,
            "exitCodeStoreAddress": exit_code_address,
            "passedClauses": spec["observableClauses"],
            "unmeasuredClauses": spec["unobservableClauses"],
        })
    report = make_report("zkvm_exit", checked.artifact, reports)
    report["scope"] = "one concrete contract check per evidence vector"
    return report


if __name__ == "__main__":
    raise SystemExit(run_cli(validate))
