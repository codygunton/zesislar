#!/usr/bin/env python3
"""Check observable writeSuccess contract clauses for concrete QEMU runs."""

from __future__ import annotations

from contract_evidence import (check_pc_extent, check_preserved_integer_registers,
                               complete_registers, context, make_report, named_binding,
                               one, run_cli)


def validate(spec: dict, manifest: dict, bindings: dict, evidence: dict) -> dict:
    if spec.get("contract") != "writeSuccess":
        raise ValueError("unexpected contract evidence specification")
    checked = context(spec["qualified"], manifest, bindings, evidence)
    boundary = checked.boundary
    exit_pc = one(boundary["exitPcs"], "writeSuccess exit PC")
    if named_binding(checked.binding, "decoded").get("addressRegister") != 10:
        raise ValueError("writeSuccess decoded binding differs")
    prefixes = evidence["initializedDecodedPrefixes"]
    reports = []
    for run in checked.runs:
        label = run.vector["label"]
        before = complete_registers(run.occurrence["entryRegisters"], f"writeSuccess entry for {label}")
        after = complete_registers(run.occurrence["afterRegisters"], f"writeSuccess exit for {label}")
        stack, decoded_address = before[2], before[10]
        if (before[1] != exit_pc or decoded_address != stack + 0x20 or
                stack < 0x880 or stack >= 2 ** 64 or stack % 16):
            raise ValueError(f"writeSuccess entry ABI differs for {label}")
        prefix = one([row for row in prefixes if row["vector"] == label],
                     f"initialized decoded prefix for {label}")
        if prefix["address"] != decoded_address or len(bytes.fromhex(prefix["bytes"])) != 848:
            raise ValueError(f"writeSuccess decoded prefix differs for {label}")
        chunks = run.occurrence["hostWrites"]
        if not chunks:
            raise ValueError(f"writeSuccess emitted no observation for {label}")
        output = b"".join(bytes.fromhex(row["bytes"]) for row in chunks)
        if not output.startswith(bytes.fromhex(spec["successPrefixHex"])):
            raise ValueError(f"writeSuccess observation framing differs for {label}")
        terminal = one(run.vector["terminalOutputs"], f"terminal output for {label}")
        final_chunk = chunks[-1]
        if (terminal["address"] != final_chunk["address"] or
                terminal["bytes"] != final_chunk["bytes"]):
            raise ValueError(f"writeSuccess stdout append differs for {label}")
        frame_start = stack - 0x880
        for row in run.occurrence["memoryWrites"]:
            address, end = row["address"], row["address"] + row["width"]
            in_frame = frame_start <= address and end <= stack
            in_context = ((address == spec["ioContextAddress"] + 8 or
                           address == spec["ioContextAddress"] + 16) and row["width"] == 8)
            if not in_frame and not in_context:
                raise ValueError(f"writeSuccess memory frame differs for {label}")
        step_count = check_pc_extent(run, set(boundary["executionPcs"]), exit_pc)
        check_preserved_integer_registers(before, after, spec["calleePreservedIntegerRegisters"],
                                          f"writeSuccess for {label}")
        reports.append({"vector": label, "verdict": "observable clauses passed",
                        "entryPc": boundary["entryPc"], "returnPc": exit_pc,
                        "decodedAddress": decoded_address, "outputSize": len(output),
                        "outputChunkCount": len(chunks), "observedStepCount": step_count,
                        "passedClauses": spec["observableClauses"],
                        "unmeasuredClauses": spec["unobservableClauses"]})
    return make_report("writeSuccess", checked.artifact, reports)


if __name__ == "__main__":
    raise SystemExit(run_cli(validate))
