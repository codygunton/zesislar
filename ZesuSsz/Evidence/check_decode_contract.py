#!/usr/bin/env python3
"""Check observable sszDecode contract clauses for concrete QEMU runs."""

from __future__ import annotations

from contract_evidence import (check_pc_extent, check_preserved_integer_registers,
                               complete_registers, context, make_report, named_binding,
                               one, run_cli, vector_record)


def validate(spec: dict, manifest: dict, bindings: dict, evidence: dict) -> dict:
    if spec.get("contract") != "sszDecode":
        raise ValueError("unexpected contract evidence specification")
    checked = context(spec["qualified"], manifest, bindings, evidence, True)
    boundary = checked.boundary
    exit_pc = one(boundary["exitPcs"], "sszDecode exit PC")
    if named_binding(checked.binding, "alloc").get("addressRegister") != 11:
        raise ValueError("sszDecode allocator binding differs")
    size_rows = evidence["boundaryBindingValidation"]["decodeInputBindings"]
    outcomes = evidence["sszDecodeObservedRuns"]
    prefixes = evidence["initializedDecodedPrefixes"]
    reports = []
    for run in checked.runs:
        label = run.vector["label"]
        before = complete_registers(run.occurrence["entryRegisters"], f"sszDecode entry for {label}")
        after = complete_registers(run.occurrence["afterRegisters"], f"sszDecode exit for {label}")
        stack, result_address, allocator_address = before[2], before[10], before[11]
        input_address, input_size = before[12], before[13]
        if (before[1] != exit_pc or result_address != stack + 0x20 or
                allocator_address != stack + 0x10 or stack < 0xbb0 or stack % 16 or
                stack + 0x380 >= 2 ** 64 or input_address + input_size > 2 ** 64 or
                not (stack + 0x380 <= input_address or
                     input_address + input_size <= stack - 0xbb0)):
            raise ValueError(f"sszDecode entry ABI differs for {label}")
        if input_size != vector_record(size_rows, label, "input size")["inputSize"]:
            raise ValueError(f"sszDecode input size differs for {label}")
        descriptor_loads = {(row["address"], row["width"], row["value"])
                            for row in run.observed["memoryAccesses"] if row["kind"] == "load"}
        if not any(address == stack + 0x10 and width == 8 for address, width, _ in descriptor_loads):
            raise ValueError(f"sszDecode allocator state load differs for {label}")
        if (stack + 0x18, 8, spec["allocatorVtableAddress"]) not in descriptor_loads:
            raise ValueError(f"sszDecode allocator vtable differs for {label}")
        if any(input_address < row["address"] + row["width"] and
               row["address"] < input_address + input_size
               for row in run.occurrence["memoryWrites"]):
            raise ValueError(f"sszDecode changed its input bytes for {label}")
        outcome = vector_record(outcomes, label, "decode outcome")["outcome"]
        status_writes = [row for row in run.occurrence["memoryWrites"]
                         if row["address"] == stack + 0x370 and row["width"] == 2]
        status = one(status_writes, f"sszDecode status write for {label}")["value"]
        if (outcome == "success") != (status == 0):
            raise ValueError(f"sszDecode status outcome differs for {label}")
        captured = [row for row in prefixes if row["vector"] == label]
        if outcome == "success":
            prefix = one(captured, f"initialized decoded prefix for {label}")
            if prefix["address"] != result_address or len(bytes.fromhex(prefix["bytes"])) != 848:
                raise ValueError(f"sszDecode initialized result differs for {label}")
        elif captured:
            raise ValueError(f"sszDecode failure has a decoded prefix for {label}")
        step_count = check_pc_extent(run, set(boundary["executionPcs"]), exit_pc)
        check_preserved_integer_registers(before, after, spec["calleePreservedIntegerRegisters"],
                                          f"sszDecode for {label}")
        reports.append({"vector": label, "verdict": "observable clauses passed",
                        "entryPc": boundary["entryPc"], "returnPc": exit_pc,
                        "inputAddress": input_address, "inputSize": input_size,
                        "outcome": outcome, "status": status,
                        "observedStepCount": step_count,
                        "passedClauses": spec["observableClauses"],
                        "unmeasuredClauses": spec["unobservableClauses"]})
    return make_report("sszDecode", checked.artifact, reports)


if __name__ == "__main__":
    raise SystemExit(run_cli(validate))
