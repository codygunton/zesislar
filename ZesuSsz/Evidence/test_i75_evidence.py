"""Reject changed boundaries and stronger claims in the retained I75 evidence."""
import copy
import hashlib
import json
from pathlib import Path
import tempfile
import unittest

from check_i75_evidence import INDEX, archived, check


class I75EvidenceTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.index = json.loads(INDEX.read_text())

    def test_retained_index(self):
        result = check(self.index)
        self.assertEqual(result["diagnostic_boundaries"], 15)
        self.assertFalse(result["native_closure_claim"])

    def test_missing_boundary_rejected(self):
        index = copy.deepcopy(self.index)
        index["diagnostic_cases"].pop()
        with self.assertRaisesRegex(ValueError, "boundary is missing"):
            check(index)

    def test_changed_groups_rejected(self):
        index = copy.deepcopy(self.index)
        index["diagnostic_cases"][-1]["actual_groups"]["active"] = 0
        with self.assertRaisesRegex(ValueError, "actual_groups"):
            check(index)

    def test_closure_and_concrete_witness_claims_rejected(self):
        for field in ("native_closure_claim", "first_global_chronology_claim",
                      "concrete_6960_witness_claim"):
            with self.subTest(field=field):
                index = copy.deepcopy(self.index)
                index[field] = True
                with self.assertRaisesRegex(ValueError, "concrete witness"):
                    check(index)

    def test_activated_pass_rejected(self):
        index = copy.deepcopy(self.index)
        index["repair_ON"] = "released"
        with self.assertRaisesRegex(ValueError, "future native pass"):
            check(index)

    def test_archive_uses_exact_retained_bytes(self):
        with tempfile.TemporaryDirectory() as directory:
            original = Path(directory) / "original"
            retained = Path(directory) / "retained"
            original.write_bytes(b"current bytes")
            retained.write_bytes(b"historical bytes")
            reference = {"path": str(original), "archive_path": str(retained),
                         "sha256": hashlib.sha256(retained.read_bytes()).hexdigest()}
            self.assertEqual(archived(reference), b"historical bytes")
            retained.write_bytes(b"changed bytes")
            with self.assertRaisesRegex(ValueError, "bound file changed"):
                archived(reference)


if __name__ == "__main__":
    unittest.main()
