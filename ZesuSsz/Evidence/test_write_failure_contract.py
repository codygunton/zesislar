#!/usr/bin/env python3
import copy
import unittest

from check_write_failure_contract import validate


class WriteFailureContractTest(unittest.TestCase):
    def setUp(self):
        self.spec = {
            "contract": "writeFailure", "qualified": "writer", "returnAddressRegister": 1,
            "ioContextAddress": 1000, "failureRecordHex": "5a53535a0100",
            "calleePreservedIntegerRegisters": [1, 2, 8],
            "observableClauses": ["failureObservation"],
            "unobservableClauses": ["stdinUnchanged"],
        }
        artifact = {"sha256": "same"}
        self.manifest = {"artifact": artifact, "instances": [{
            "qualified": "writer", "entryPc": 4,
            "executionPcs": [4, 8, 12], "exitPcs": [16],
        }]}
        self.bindings = {"artifact": artifact, "instances": [{
            "qualified": "writer", "bindings": [],
        }]}
        before = [0] * 32
        before[1], before[2], before[8] = 16, 200, 300
        after = copy.deepcopy(before)
        occurrence = {
            "entryRegisters": {"available": 2 ** 32 - 1, "values": before},
            "afterRegisters": {"available": 2 ** 32 - 1, "values": after},
            "afterPc": 16, "executedInstructionCount": 3,
            "hostWrites": [{"pc": 8, "address": 2000, "bytes": "5a53535a0100"}],
            "memoryWrites": [
                {"kind": "store", "pc": 8, "address": 1008, "width": 8, "value": 2000},
                {"kind": "store", "pc": 12, "address": 1016, "width": 8, "value": 6},
            ],
        }
        self.evidence = {"artifact": artifact, "vectors": [{
            "label": "invalid", "terminalOutputs": [
                {"address": 2000, "bytes": "5a53535a0100"}],
            "instances": [{"qualified": "writer", "entryReached": True,
                           "executedExtentPcs": [4, 8, 12],
                           "occurrences": [occurrence]}],
        }]}

    def test_accepts_observed_contract(self):
        report = validate(self.spec, self.manifest, self.bindings, self.evidence)
        self.assertEqual(report["runs"][0]["observedStepCount"], 3)

    def test_rejects_non_failure_record(self):
        evidence = copy.deepcopy(self.evidence)
        evidence["vectors"][0]["instances"][0]["occurrences"][0]["hostWrites"][0]["bytes"] = "00"
        with self.assertRaisesRegex(ValueError, "not failure"):
            validate(self.spec, self.manifest, self.bindings, evidence)

    def test_rejects_extra_memory_write(self):
        evidence = copy.deepcopy(self.evidence)
        writes = evidence["vectors"][0]["instances"][0]["occurrences"][0]["memoryWrites"]
        writes.append({"kind": "store", "pc": 12, "address": 2000, "width": 8, "value": 0})
        with self.assertRaisesRegex(ValueError, "memory frame differs"):
            validate(self.spec, self.manifest, self.bindings, evidence)

    def test_rejects_changed_preserved_register(self):
        evidence = copy.deepcopy(self.evidence)
        evidence["vectors"][0]["instances"][0]["occurrences"][0]["afterRegisters"]["values"][8] = 9
        with self.assertRaisesRegex(ValueError, "changed preserved x8"):
            validate(self.spec, self.manifest, self.bindings, evidence)

    def test_rejects_wrong_return_address(self):
        evidence = copy.deepcopy(self.evidence)
        evidence["vectors"][0]["instances"][0]["occurrences"][0]["entryRegisters"]["values"][1] = 20
        with self.assertRaisesRegex(ValueError, "return address differs"):
            validate(self.spec, self.manifest, self.bindings, evidence)

    def test_rejects_stdout_mismatch(self):
        evidence = copy.deepcopy(self.evidence)
        evidence["vectors"][0]["terminalOutputs"][0]["bytes"] = "00"
        with self.assertRaisesRegex(ValueError, "stdout append differs"):
            validate(self.spec, self.manifest, self.bindings, evidence)

    def test_rejects_wrong_step_count(self):
        evidence = copy.deepcopy(self.evidence)
        evidence["vectors"][0]["instances"][0]["occurrences"][0]["executedInstructionCount"] = 0
        with self.assertRaisesRegex(ValueError, "step count differs"):
            validate(self.spec, self.manifest, self.bindings, evidence)


if __name__ == "__main__":
    unittest.main()
