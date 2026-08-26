#!/usr/bin/env python3

import unittest

from check_coarse_contracts import EXPECTED, validate


class CoarseContractTest(unittest.TestCase):
    def manifest(self) -> dict:
        return {"instances": [
            {"qualified": name, "entryPc": pc}
            for name, pc in EXPECTED.items()
        ]}

    def test_fixed_boundary_passes(self) -> None:
        validate(self.manifest())

    def test_mutated_entry_is_rejected(self) -> None:
        manifest = self.manifest()
        manifest["instances"][0]["entryPc"] += 4
        with self.assertRaises(ValueError):
            validate(manifest)

    def test_added_contract_is_rejected(self) -> None:
        manifest = self.manifest()
        manifest["instances"].append({"qualified": "extra", "entryPc": 0})
        with self.assertRaises(ValueError):
            validate(manifest)


if __name__ == "__main__":
    unittest.main()
