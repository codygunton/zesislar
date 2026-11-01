"""Reject changed boundaries and stronger claims in the retained I75 evidence."""
import copy
import hashlib
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

from _evidence_fixtures import repository

from check_i75_evidence import CLEANUP_STATUS, INDEX, ROOT, archived, check


class I75EvidenceTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.index = json.loads((repository() / "ZesuSsz/Evidence/i75/INDEX.json").read_text())

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


    def test_absent_worktree_artifact_requires_the_exact_status(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / '.worktrees/retired/raw.json'
            reference = {'path': str(path), 'sha256': '0' * 64, 'status': CLEANUP_STATUS}
            self.assertIsNone(archived(reference))
            for status in (None, 'removed', CLEANUP_STATUS + '.'):
                candidate = dict(reference)
                if status is None:
                    candidate.pop('status')
                else:
                    candidate['status'] = status
                with self.subTest(status=status), self.assertRaises(ValueError):
                    archived(candidate)

    def test_cleanup_status_does_not_apply_outside_worktrees(self):
        with tempfile.TemporaryDirectory() as directory:
            reference = {'path': str(Path(directory) / 'missing.json'),
                         'sha256': '0' * 64, 'status': CLEANUP_STATUS}
            with self.assertRaises(ValueError):
                archived(reference)

    def test_present_cleanup_artifact_still_requires_its_exact_hash(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / '.worktrees/retired/raw.json'
            path.parent.mkdir(parents=True)
            path.write_bytes(b'retained')
            reference = {'path': str(path), 'sha256': hashlib.sha256(b'retained').hexdigest(),
                         'status': CLEANUP_STATUS}
            self.assertEqual(archived(reference), b'retained')
            path.write_bytes(b'changed')
            with self.assertRaisesRegex(ValueError, 'bound file changed'):
                archived(reference)

    def test_missing_raw_history_never_verifies_archive_or_exports(self):
        main, correction = self.index['main_record'], self.index['context_correction']
        def retained_reports_only(reference, root=ROOT):
            return archived(reference, root) if reference in (main, correction) else None
        with patch('check_i75_evidence.archived', side_effect=retained_reports_only):
            result = check(self.index, check_archive=True)
        self.assertTrue(result['retained_metadata_and_groups_verified'])
        self.assertEqual(result['archive_reference_coverage'], CLEANUP_STATUS)
        self.assertEqual(result['archive_objects_verified'], 0)
        self.assertEqual(result['raw_sources_verified'], 0)
        self.assertEqual(result['raw_exports_verified'], 0)
        self.assertFalse(result['native_closure_claim'])


if __name__ == "__main__":
    unittest.main()
