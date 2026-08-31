#!/usr/bin/env python3
import copy
import unittest

from check_allocator_get_contract import validate as validate_allocator
from check_decode_contract import validate as validate_decode
from check_read_input_contract import validate as validate_read
from check_write_success_contract import validate as validate_success


ARTIFACT = {"sha256": "same"}
PRESERVED = [1, 2, 8]


def snapshot(values):
    return {"available": 2 ** 32 - 1, "values": values}


def fixture(qualified, occurrence, accesses=None, bindings=None, terminal=None):
    manifest = {"artifact": ARTIFACT, "instances": [{
        "qualified": qualified, "entryPc": 4, "executionPcs": [4, 8, 12], "exitPcs": [16],
    }]}
    boundary_bindings = {"artifact": ARTIFACT, "instances": [{
        "qualified": qualified, "bindings": bindings or [],
    }]}
    evidence = {"artifact": ARTIFACT, "vectors": [{
        "label": "sample", "terminalOutputs": terminal or [], "instances": [{
            "qualified": qualified, "entryReached": True, "executedExtentPcs": [4, 8, 12],
            "memoryAccesses": accesses or [], "occurrences": [occurrence],
        }],
    }]}
    return manifest, boundary_bindings, evidence


class RemainingContractTest(unittest.TestCase):
    def test_read_input_and_rejects_wrong_result_slot(self):
        before = [0] * 32
        before[1], before[2], before[8], before[10], before[11] = 16, 200, 300, 400, 408
        occurrence = {
            "entryRegisters": snapshot(before), "afterRegisters": snapshot(copy.deepcopy(before)),
            "afterPc": 16, "executedInstructionCount": 3, "hostWrites": [],
            "memoryWrites": [
                {"kind": "store", "pc": 8, "address": 400, "width": 8, "value": 500},
                {"kind": "store", "pc": 12, "address": 408, "width": 8, "value": 6}],
        }
        manifest, bindings, evidence = fixture(
            "reader", occurrence,
            [{"kind": "load", "pc": 4, "address": 600, "width": 8, "value": 6}],
            [{"name": "buffer", "machineRegister": 10},
             {"name": "size", "machineRegister": 11}])
        evidence["boundaryBindingValidation"] = {"decodeInputBindings": [
            {"vector": "sample", "inputSize": 6}]}
        spec = {"contract": "readInput", "qualified": "reader", "inputBufferAddress": 500,
                "ioContextAddress": 600, "maxInputSize": 100,
                "calleePreservedIntegerRegisters": PRESERVED,
                "observableClauses": [], "unobservableClauses": []}
        self.assertEqual(validate_read(spec, manifest, bindings, evidence)["runs"][0]["inputSize"], 6)
        bad = copy.deepcopy(evidence)
        bad["vectors"][0]["instances"][0]["occurrences"][0]["memoryWrites"][1]["value"] = 7
        with self.assertRaisesRegex(ValueError, "memory frame differs"):
            validate_read(spec, manifest, bindings, bad)

    def test_allocator_get_and_rejects_wrong_vtable(self):
        before = [0] * 32
        before[1], before[2], before[8] = 16, 400, 300
        after = copy.deepcopy(before)
        after[10], after[11], after[12], after[13] = 700, 800, 500, 6
        occurrence = {
            "entryRegisters": snapshot(before), "afterRegisters": snapshot(after),
            "afterPc": 16, "executedInstructionCount": 3, "hostWrites": [],
            "memoryWrites": [
                {"kind": "store", "pc": 8, "address": 416, "width": 8, "value": 700},
                {"kind": "store", "pc": 12, "address": 424, "width": 8, "value": 800}],
        }
        accesses = [{"kind": "load", "address": 400, "width": 8, "value": 500},
                    {"kind": "load", "address": 408, "width": 8, "value": 6}]
        manifest, bindings, evidence = fixture("allocator", occurrence, accesses)
        spec = {"contract": "allocatorGet", "qualified": "allocator",
                "allocatorStateAddress": 700, "allocatorVtableAddress": 800,
                "calleePreservedIntegerRegisters": PRESERVED,
                "observableClauses": [], "unobservableClauses": []}
        self.assertEqual(validate_allocator(spec, manifest, bindings, evidence)["runs"][0]["inputSize"], 6)
        bad = copy.deepcopy(evidence)
        bad["vectors"][0]["instances"][0]["occurrences"][0]["afterRegisters"]["values"][11] = 801
        with self.assertRaisesRegex(ValueError, "result registers differ"):
            validate_allocator(spec, manifest, bindings, bad)

    def test_decode_and_rejects_wrong_status(self):
        before = [0] * 32
        before[1], before[2], before[8] = 16, 0x1000, 300
        before[10], before[11], before[12], before[13] = 0x1020, 0x1010, 0x2000, 6
        after = copy.deepcopy(before)
        occurrence = {
            "entryRegisters": snapshot(before), "afterRegisters": snapshot(after),
            "afterPc": 16, "executedInstructionCount": 3, "hostWrites": [],
            "memoryWrites": [{"kind": "store", "pc": 12, "address": 0x1370,
                              "width": 2, "value": 0}],
        }
        accesses = [{"kind": "load", "address": 0x1010, "width": 8, "value": 700},
                    {"kind": "load", "address": 0x1018, "width": 8, "value": 800}]
        manifest, bindings, evidence = fixture(
            "decoder", occurrence, accesses, [{"name": "alloc", "addressRegister": 11}])
        evidence["boundaryBindingValidation"] = {"decodeInputBindings": [
            {"vector": "sample", "inputSize": 6}]}
        evidence["sszDecodeObservedRuns"] = [{"vector": "sample", "outcome": "success"}]
        evidence["initializedDecodedPrefixes"] = [
            {"vector": "sample", "address": 0x1020, "bytes": "00" * 848}]
        spec = {"contract": "sszDecode", "qualified": "decoder",
                "allocatorVtableAddress": 800,
                "calleePreservedIntegerRegisters": PRESERVED,
                "observableClauses": [], "unobservableClauses": []}
        self.assertEqual(validate_decode(spec, manifest, bindings, evidence)["runs"][0]["outcome"],
                         "success")
        bad = copy.deepcopy(evidence)
        bad["vectors"][0]["instances"][0]["occurrences"][0]["memoryWrites"][0]["value"] = 1
        with self.assertRaisesRegex(ValueError, "status outcome differs"):
            validate_decode(spec, manifest, bindings, bad)

    def test_write_success_and_rejects_wrong_prefix(self):
        before = [0] * 32
        before[1], before[2], before[8], before[10] = 16, 0x1000, 300, 0x1020
        after = copy.deepcopy(before)
        chunks = [{"pc": 8, "address": 600, "bytes": "5a53535a0101"},
                  {"pc": 8, "address": 700, "bytes": "aabb"}]
        occurrence = {
            "entryRegisters": snapshot(before), "afterRegisters": snapshot(after),
            "afterPc": 16, "executedInstructionCount": 3, "hostWrites": chunks,
            "memoryWrites": [{"kind": "store", "pc": 12, "address": 0xff0,
                              "width": 8, "value": 1}],
        }
        manifest, bindings, evidence = fixture(
            "success", occurrence, bindings=[{"name": "decoded", "addressRegister": 10}],
            terminal=[{"address": 700, "bytes": "aabb"}])
        evidence["initializedDecodedPrefixes"] = [
            {"vector": "sample", "address": 0x1020, "bytes": "00" * 848}]
        spec = {"contract": "writeSuccess", "qualified": "success",
                "ioContextAddress": 10000, "successPrefixHex": "5a53535a0101",
                "calleePreservedIntegerRegisters": PRESERVED,
                "observableClauses": [], "unobservableClauses": []}
        self.assertEqual(validate_success(spec, manifest, bindings, evidence)["runs"][0]["outputSize"], 8)
        bad = copy.deepcopy(evidence)
        bad["vectors"][0]["instances"][0]["occurrences"][0]["hostWrites"][0]["bytes"] = "00"
        with self.assertRaisesRegex(ValueError, "framing differs"):
            validate_success(spec, manifest, bindings, bad)


if __name__ == "__main__":
    unittest.main()
