#!/usr/bin/env python3
"""Check observable allocatorGet contract clauses for concrete QEMU runs."""

from __future__ import annotations

from contract_evidence import (check_pc_extent, check_preserved_integer_registers,
                               complete_registers, context, make_report, one, run_cli)


def validate(spec: dict, manifest: dict, bindings: dict, evidence: dict) -> dict:
    if spec.get("contract") != "allocatorGet":
        raise ValueError("unexpected contract evidence specification")
    checked = context(spec["qualified"], manifest, bindings, evidence, True)
    boundary = checked.boundary
    exit_pc = one(boundary["exitPcs"], "allocatorGet exit PC")
    reports = []
    for run in checked.runs:
        label = run.vector["label"]
        before = complete_registers(run.occurrence["entryRegisters"], f"allocatorGet entry for {label}")
        after = complete_registers(run.occurrence["afterRegisters"], f"allocatorGet exit for {label}")
        stack = before[2]
        if stack % 8 or stack + 0x20 >= 2 ** 64:
            raise ValueError(f"allocatorGet stack alignment differs for {label}")
        loads = {(row["address"], row["width"]): row["value"]
                 for row in run.observed["memoryAccesses"] if row["kind"] == "load"}
        if (stack, 8) not in loads or (stack + 8, 8) not in loads:
            raise ValueError(f"allocatorGet input slice loads differ for {label}")
        input_address, input_size = loads[(stack, 8)], loads[(stack + 8, 8)]
        if not (stack + 0x20 <= input_address or input_address + input_size <= stack + 0x10):
            raise ValueError(f"allocatorGet address separation differs for {label}")
        state_address, vtable_address = after[10], after[11]
        if (after[2] != stack or after[12] != input_address or after[13] != input_size or
                state_address != spec["allocatorStateAddress"] or
                vtable_address != spec["allocatorVtableAddress"]):
            raise ValueError(f"allocatorGet result registers differ for {label}")
        expected_writes = {(stack + 0x10, 8, state_address), (stack + 0x18, 8, vtable_address)}
        actual_writes = {(row["address"], row["width"], row["value"])
                         for row in run.occurrence["memoryWrites"]}
        if actual_writes != expected_writes or len(run.occurrence["memoryWrites"]) != 2:
            raise ValueError(f"allocatorGet memory frame differs for {label}")
        step_count = check_pc_extent(run, set(boundary["executionPcs"]), exit_pc)
        check_preserved_integer_registers(before, after, spec["calleePreservedIntegerRegisters"],
                                          f"allocatorGet for {label}")
        reports.append({"vector": label, "verdict": "observable clauses passed",
                        "entryPc": boundary["entryPc"], "returnPc": exit_pc,
                        "inputAddress": input_address, "inputSize": input_size,
                        "allocatorStateAddress": state_address,
                        "allocatorVtableAddress": vtable_address,
                        "observedStepCount": step_count,
                        "passedClauses": spec["observableClauses"],
                        "unmeasuredClauses": spec["unobservableClauses"]})
    return make_report("allocatorGet", checked.artifact, reports)


if __name__ == "__main__":
    raise SystemExit(run_cli(validate))
