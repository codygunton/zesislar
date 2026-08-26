#!/usr/bin/env python3
"""Check the observable writeFailure contract clauses for concrete QEMU runs."""

from __future__ import annotations

from contract_evidence import (check_pc_extent, complete_registers, context,
                               make_report, one, run_cli)


def validate(spec: dict, manifest: dict, bindings: dict, evidence: dict) -> dict:
    if spec.get("contract") != "writeFailure":
        raise ValueError("unexpected contract evidence specification")
    checked = context(spec["qualified"], manifest, bindings, evidence)
    boundary = checked.boundary
    exit_pc = one(boundary["exitPcs"], "writeFailure exit PC")
    execution_pcs = set(boundary["executionPcs"])
    expected_bytes = spec["failureRecordHex"]
    output_address_word = spec["ioContextAddress"] + 8
    output_length_word = spec["ioContextAddress"] + 16
    reports = []
    for run in checked.runs:
        label = run.vector["label"]
        before = complete_registers(run.occurrence["entryRegisters"],
                                    f"writeFailure entry for {label}")
        after = complete_registers(run.occurrence["afterRegisters"],
                                   f"writeFailure exit for {label}")
        return_register = spec["returnAddressRegister"]
        if before[return_register] != exit_pc:
            raise ValueError(f"writeFailure return address differs for {label}")
        step_count = check_pc_extent(run, execution_pcs, exit_pc)

        output = one(run.occurrence["hostWrites"], f"writeFailure output for {label}")
        if output["bytes"] != expected_bytes:
            raise ValueError(f"writeFailure observation is not failure for {label}")
        expected_writes = {
            (output_address_word, 8, output["address"]),
            (output_length_word, 8, len(bytes.fromhex(expected_bytes))),
        }
        actual_writes = {(write["address"], write["width"], write["value"])
                         for write in run.occurrence["memoryWrites"]
                         if write["kind"] == "store" and write["pc"] in execution_pcs}
        if actual_writes != expected_writes or len(run.occurrence["memoryWrites"]) != 2:
            raise ValueError(f"writeFailure memory frame differs for {label}")

        for register in spec["calleePreservedIntegerRegisters"]:
            if before[register] != after[register]:
                raise ValueError(f"writeFailure changed preserved x{register} for {label}")
        terminal = one(run.vector["terminalOutputs"], f"terminal output for {label}")
        if terminal["address"] != output["address"] or terminal["bytes"] != expected_bytes:
            raise ValueError(f"writeFailure stdout append differs for {label}")

        reports.append({
            "vector": label,
            "verdict": "observable clauses passed",
            "entryPc": boundary["entryPc"],
            "returnPc": exit_pc,
            "observedStepCount": step_count,
            "failureRecordHex": expected_bytes,
            "passedClauses": spec["observableClauses"],
            "unmeasuredClauses": spec["unobservableClauses"],
        })
    return make_report("writeFailure", checked.artifact, reports)


if __name__ == "__main__":
    raise SystemExit(run_cli(validate))
