#!/usr/bin/env python3
import copy
import unittest

from check_zkvm_exit_contract import validate


class ZkvmExitContractTest(unittest.TestCase):
    def setUp(self):
        self.spec = {
            "contract": "zkvm_exit", "argumentRegister": 10,
            "ioContextAddress": 1000, "exitCodeOffset": 24,
            "observableClauses": ["exitCodeStore"],
            "unobservableClauses": ["ConfiguredMachinePre"],
        }
        artifact = {"sha256": "same"}
        self.manifest = {"artifact": artifact, "instances": [{
            "qualified": "zkvm_exit", "entryPc": 4,
            "executionPcs": [4, 8, 12, 16], "exitPcs": [16],
        }]}
        self.bindings = {"artifact": artifact, "instances": [{
            "qualified": "zkvm_exit", "bindings": [
                {"name": "code", "machineRegister": 10}],
        }]}
        registers = [0] * 32
        registers[10] = 7
        self.evidence = {"artifact": artifact, "vectors": [{
            "label": "sample",
            "terminalOutputs": [{"address": 2000, "bytes": "aabb"}],
            "instances": [{
                "qualified": "writer", "hostWrites": [
                    {"address": 2000, "bytes": "aabb"}],
                "occurrences": [],
            }, {
                "qualified": "zkvm_exit", "entryReached": True,
                "executedExtentPcs": [4, 8, 12, 16],
                "hostWrites": [], "occurrences": [{
                    "entryRegisters": {"available": 2 ** 32 - 1, "values": registers},
                    "afterPc": 16, "executedInstructionCount": 4, "hostWrites": [],
                    "memoryWrites": [{"kind": "store", "pc": 12,
                                      "address": 1024, "width": 8, "value": 7}],
                }],
            }],
        }]}

    def test_accepts_observed_contract(self):
        report = validate(self.spec, self.manifest, self.bindings, self.evidence)
        self.assertEqual(report["runs"][0]["code"], 7)
        self.assertEqual(report["runs"][0]["observedStepCount"], 3)

    def test_rejects_wrong_exit_code(self):
        evidence = copy.deepcopy(self.evidence)
        evidence["vectors"][0]["instances"][1]["occurrences"][0]["memoryWrites"][0]["value"] = 8
        with self.assertRaisesRegex(ValueError, "memory frame differs"):
            validate(self.spec, self.manifest, self.bindings, evidence)

    def test_rejects_extra_memory_write(self):
        evidence = copy.deepcopy(self.evidence)
        writes = evidence["vectors"][0]["instances"][1]["occurrences"][0]["memoryWrites"]
        writes.append({"kind": "store", "pc": 8, "address": 2000, "width": 8, "value": 0})
        with self.assertRaisesRegex(ValueError, "memory frame differs"):
            validate(self.spec, self.manifest, self.bindings, evidence)

    def test_rejects_changed_stdout(self):
        evidence = copy.deepcopy(self.evidence)
        evidence["vectors"][0]["instances"][1]["occurrences"][0]["hostWrites"] = [
            {"address": 2000, "bytes": "cc"}]
        with self.assertRaisesRegex(ValueError, "changed stdout"):
            validate(self.spec, self.manifest, self.bindings, evidence)

    def test_rejects_terminal_stdout_mismatch(self):
        evidence = copy.deepcopy(self.evidence)
        evidence["vectors"][0]["terminalOutputs"][0]["bytes"] = "cc"
        with self.assertRaisesRegex(ValueError, "terminal stdout differs"):
            validate(self.spec, self.manifest, self.bindings, evidence)

    def test_rejects_wrong_step_count(self):
        evidence = copy.deepcopy(self.evidence)
        evidence["vectors"][0]["instances"][1]["occurrences"][0]["executedInstructionCount"] = 5
        with self.assertRaisesRegex(ValueError, "step count differs"):
            validate(self.spec, self.manifest, self.bindings, evidence)


if __name__ == "__main__":
    unittest.main()
