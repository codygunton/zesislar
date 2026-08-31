#!/usr/bin/env python3

import copy
import unittest

from check_level1_proof_map import validate


def fixture():
    ids = [f"i{index}" for index in range(6)]
    manifest = {"instances": [{"id": item} for item in ids]}
    evidence = {"vectors": [{"instances": [{"id": item} for item in ids]}]}
    bindings = {"instances": [{"id": item} for item in ids]}
    proof_map = {
        "boundaries": [{"instanceId": item, "evidenceStatus": "captured",
                         "contractStatus": "specified_assumption", "proofStatus": "not_started"}
                        for item in ids],
        "refinementGraph": {"nodes": [{"proofStatus": "not_started"}]},
        "formalCoverage": {"directPcCount": 0, "boundaryRegionPcCount": 6,
                           "endpointPcCount": 10},
    }
    return proof_map, manifest, evidence, bindings


class Level1ProofMapTest(unittest.TestCase):
    def test_honest_payload_passes(self):
        validate(*fixture())

    def test_missing_boundary_is_rejected(self):
        documents = list(fixture())
        documents[0] = copy.deepcopy(documents[0])
        documents[0]["boundaries"].pop()
        with self.assertRaisesRegex(ValueError, "exact six"):
            validate(*documents)

    def test_proof_claim_is_rejected(self):
        documents = list(fixture())
        documents[0] = copy.deepcopy(documents[0])
        documents[0]["boundaries"][0]["proofStatus"] = "proved"
        with self.assertRaisesRegex(ValueError, "proof claim"):
            validate(*documents)


if __name__ == "__main__":
    unittest.main()
