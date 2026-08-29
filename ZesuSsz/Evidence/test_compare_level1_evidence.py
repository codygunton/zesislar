#!/usr/bin/env python3

import copy
import unittest

from compare_level1_evidence import compare


def report(base=0x7FFFFFF00000):
    return {
        "sszDecodeObservedRuns": [{
            "outcome": "success", "successResultAddress": base,
        }],
        "vectors": [{"register": base - 32, "fixedAddress": 0x2001A000}],
    }


class CompareEvidenceTest(unittest.TestCase):
    def test_stack_relocation_is_ignored(self):
        compare(report(), report(0x7FFFFFE00000))

    def test_non_stack_change_is_rejected(self):
        changed = copy.deepcopy(report())
        changed["vectors"][0]["fixedAddress"] += 1
        with self.assertRaisesRegex(ValueError, "differs"):
            compare(report(), changed)

    def test_missing_success_is_rejected(self):
        changed = report()
        changed["sszDecodeObservedRuns"] = []
        with self.assertRaisesRegex(ValueError, "one successful"):
            compare(report(), changed)


if __name__ == "__main__":
    unittest.main()
