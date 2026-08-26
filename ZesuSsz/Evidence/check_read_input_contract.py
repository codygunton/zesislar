#!/usr/bin/env python3
"""Check observable readInput contract clauses for concrete QEMU runs."""

from __future__ import annotations

from contract_evidence import (check_pc_extent, check_preserved_integer_registers,
                               complete_registers, context, make_report, named_binding,
                               one, run_cli, vector_record)


def validate(spec: dict, manifest: dict, bindings: dict, evidence: dict) -> dict:
    if spec.get("contract") != "readInput":
        raise ValueError("unexpected contract evidence specification")
    checked = context(spec["qualified"], manifest, bindings, evidence, True)
    boundary = checked.boundary
    exit_pc = one(boundary["exitPcs"], "readInput exit PC")
    if named_binding(checked.binding, "buffer").get("machineRegister") != 10 or \
            named_binding(checked.binding, "size").get("machineRegister") != 11:
        raise ValueError("readInput ABI bindings differ")
    size_rows = evidence["boundaryBindingValidation"]["decodeInputBindings"]
    reports = []
    for run in checked.runs:
        label = run.vector["label"]
        before = complete_registers(run.occurrence["entryRegisters"], f"readInput entry for {label}")
        after = complete_registers(run.occurrence["afterRegisters"], f"readInput exit for {label}")
        size = vector_record(size_rows, label, "input size")["inputSize"]
        buffer_slot, size_slot = before[10], before[11]
        if before[1] != exit_pc or size_slot != buffer_slot + 8 or buffer_slot % 8:
            raise ValueError(f"readInput entry ABI differs for {label}")
        input_start, input_end = spec["inputBufferAddress"], spec["inputBufferAddress"] + size
        context_start, context_end = spec["ioContextAddress"], spec["ioContextAddress"] + 8
        slots_end = buffer_slot + 16
        if (slots_end >= 2 ** 64 or
                not (slots_end <= input_start or input_end <= buffer_slot) or
                not (slots_end <= context_start or context_end <= buffer_slot)):
            raise ValueError(f"readInput address separation differs for {label}")
        if not 0 <= size <= spec["maxInputSize"]:
            raise ValueError(f"readInput size exceeds its bound for {label}")
        context_loads = [row for row in run.observed["memoryAccesses"]
                         if row["kind"] == "load" and row["address"] == spec["ioContextAddress"]]
        if not any(row["width"] == 8 and row["value"] == size for row in context_loads):
            raise ValueError(f"readInput context size differs for {label}")
        expected_writes = {(buffer_slot, 8, spec["inputBufferAddress"]), (size_slot, 8, size)}
        actual_writes = {(row["address"], row["width"], row["value"])
                         for row in run.occurrence["memoryWrites"]}
        if actual_writes != expected_writes or len(run.occurrence["memoryWrites"]) != 2:
            raise ValueError(f"readInput memory frame differs for {label}")
        step_count = check_pc_extent(run, set(boundary["executionPcs"]), exit_pc)
        check_preserved_integer_registers(before, after, spec["calleePreservedIntegerRegisters"],
                                          f"readInput for {label}")
        reports.append({"vector": label, "verdict": "observable clauses passed",
                        "entryPc": boundary["entryPc"], "returnPc": exit_pc,
                        "inputSize": size, "inputAddress": input_start,
                        "observedStepCount": step_count,
                        "passedClauses": spec["observableClauses"],
                        "unmeasuredClauses": spec["unobservableClauses"]})
    return make_report("readInput", checked.artifact, reports)


if __name__ == "__main__":
    raise SystemExit(run_cli(validate))
