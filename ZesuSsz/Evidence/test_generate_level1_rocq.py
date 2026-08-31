#!/usr/bin/env python3

import copy
import unittest

from generate_level1_rocq import NAMES, generate, pc_ranges


SHA = "ab" * 32


def fixture() -> tuple[dict, dict]:
    instances = []
    functions = []
    for index, qualified in enumerate(NAMES):
        entry = 0x1000 + 0x20 * index
        instances.append({
            "qualified": qualified, "entryPc": entry,
            "instructionPcs": [entry], "absorbedInstructionPcs": [],
            "executionPcs": [entry], "exitPcs": [entry + 4],
        })
        functions.append({"name": qualified, "blocks": [{"instructions": [
            {"pc": entry, "mnemonic": "addi", "bytes": "13000000"}
        ]}]})
    main_pcs = list(range(0x1000, 0x1080, 4))
    instances[0]["executionPcs"] = [0x1000, 0x1064, 0x1068, 0x106C, 0x1070]
    functions.append({"name": "ssz_decode_root.main", "blocks": [{"instructions": [
        {"pc": pc, "mnemonic": "addi", "bytes": "13000000"} for pc in main_pcs
    ]}]})
    artifact = {"identityScope": "ELF PT_LOAD memory image", "sha256": SHA}
    return ({"artifact": artifact, "instances": instances}, {
        "artifact": artifact, "functions": functions, "functionInstances": [{
            "kind": "concrete", "parent": None, "name": "ssz_decode_root.main",
            "entryPc": 0x1000, "pcs": main_pcs,
        }],
    })


class GenerateLevel1RocqTests(unittest.TestCase):
    def test_generates_fixed_context_and_glue(self):
        manifest, cfg = fixture()
        output = generate(manifest, cfg)
        self.assertIn("Definition inputBufferAddress : Z := 0x2001a000.", output)
        self.assertIn("Definition mainGlueInstructionCount : nat := 24.", output)
        self.assertIn("Definition mainGlueWordAt1004 : Z := 0x00000013.", output)

    def test_rejects_artifact_mismatch(self):
        manifest, cfg = fixture()
        cfg = copy.deepcopy(cfg)
        cfg["artifact"] = dict(cfg["artifact"], sha256="cd" * 32)
        with self.assertRaisesRegex(ValueError, "different load images"):
            generate(manifest, cfg)

    def test_rejects_changed_inventory(self):
        manifest, cfg = fixture()
        manifest["instances"].pop()
        with self.assertRaisesRegex(ValueError, "six-instance inventory"):
            generate(manifest, cfg)

    def test_rejects_unaligned_pc(self):
        with self.assertRaisesRegex(ValueError, "not four-byte aligned"):
            pc_ranges([0x1001])


if __name__ == "__main__":
    unittest.main()
