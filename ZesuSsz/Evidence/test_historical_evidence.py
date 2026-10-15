"""Keep missing cleanup history separate from usable native proof evidence."""
import hashlib
from pathlib import Path
import tempfile
import unittest

from check_decode_item_route_repair import CLEANUP_STATUS, acceptance, bound_file, historical_file, inventory


class HistoricalEvidenceTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.path = self.root / '.worktrees/retired/_build/capture.json'
        self.reference = {'path': str(self.path), 'sha256': hashlib.sha256(b'original').hexdigest(),
                          'status': CLEANUP_STATUS}

    def test_absent_worktree_reference_needs_exact_cleanup_status(self):
        self.assertEqual(historical_file(self.reference, self.root), (self.path, None))
        for status in (None, 'removed', CLEANUP_STATUS + '.'):
            reference = dict(self.reference)
            if status is None:
                reference.pop('status')
            else:
                reference['status'] = status
            with self.subTest(status=status), self.assertRaises(ValueError):
                historical_file(reference, self.root)

    def test_present_correct_bytes_are_checked_with_or_without_status(self):
        self.path.parent.mkdir(parents=True)
        self.path.write_bytes(b'original')
        for reference in (self.reference, {k: v for k, v in self.reference.items() if k != 'status'}):
            self.assertEqual(historical_file(reference, self.root), (self.path, b'original'))

    def test_present_mismatch_is_not_excused_by_cleanup_status(self):
        self.path.parent.mkdir(parents=True)
        self.path.write_bytes(b'changed')
        with self.assertRaisesRegex(ValueError, 'bound file changed'):
            historical_file(self.reference, self.root)

    def test_non_worktree_missing_reference_is_rejected(self):
        self.reference['path'] = str(self.root / 'build/capture.json')
        with self.assertRaisesRegex(ValueError, 'exact worktree-cleanup status'):
            historical_file(self.reference, self.root)

    def test_path_cannot_escape_worktrees_with_parent_components(self):
        self.reference['path'] = str(self.root / '.worktrees/../capture.json')
        with self.assertRaises(ValueError):
            historical_file(self.reference, self.root)

    def test_missing_history_requires_a_complete_retained_hash(self):
        for value in ('', 'unknown', '0' * 63, 'G' * 64):
            self.reference['sha256'] = value
            with self.subTest(value=value), self.assertRaises(ValueError):
                historical_file(self.reference, self.root)

    def test_cleanup_status_does_not_allow_native_certificate_reads(self):
        with self.assertRaises(FileNotFoundError):
            bound_file(self.reference, self.root)

    def test_relative_worktree_reference_uses_declared_root(self):
        self.reference['path'] = '.worktrees/retired/_build/capture.json'
        self.assertEqual(historical_file(self.reference, self.root), (self.path, None))

    def test_historical_inventory_cannot_substitute_for_native_acceptance(self):
        from test_route_repair_linked_evidence import SyntheticEvidence
        fixture = SyntheticEvidence(self.root)
        fixture.index['cases'][0]['native_source'] = dict(self.reference)
        inventory(fixture.index, self.root)
        with self.assertRaises(FileNotFoundError):
            acceptance(fixture.index, fixture.bundle, self.root)
