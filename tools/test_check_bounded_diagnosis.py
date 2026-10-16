import copy
import hashlib
import json
from pathlib import Path
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parent / 'block'))
import check_bounded_diagnosis as checker


class BoundedDiagnosisTests(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)
        self.file = self.root / 'complete.marshal'
        self.file.write_bytes(b'control bytes, not a Marshal claim')
        self.reference = self.ref(self.file)
        self.bundle = checker.CheckedBundle.__new__(checker.CheckedBundle)
        self.bundle.evidence = self.root
        self.bundle.session = 'one-session'
        self.bundle.aliases = {'artifact-00000001': dict(self.reference, path=self.file.name)}
        self.capture = {'surface_policy': 'bounded-kernel-v1', 'goal': '?elided_deadbeef_0',
            'evars': {'availability': 'complete-referenced'},
            'complete_sidecar': {'artifact': '#/artifacts/artifact-00000001'},
            'fresh_evar_counter': 2, 'hyps': [], 'current_goals': [{'id': 1}],
            'shelf': [], 'given_up': [], 'completeness': {'printed_terms': 'bounded',
                'complete_terms': 'marshal-reload-and-membership-verified'}}
        self.bundle.owned_captures = {id(self.capture): self.capture}

    def ref(self, path):
        return {'path': str(path), 'sha256': hashlib.sha256(path.read_bytes()).hexdigest(),
                'bytes': path.stat().st_size}

    def test_exact_file_reference(self):
        self.assertEqual(checker.file_reference(self.file, self.reference), self.file)

    def test_changed_file_bytes(self):
        self.file.write_bytes(b'wrong bytes')
        with self.assertRaises(checker.BoundedDiagnosisError):
            checker.file_reference(self.file, self.reference)

    def test_wrong_file_size(self):
        with self.assertRaises(checker.BoundedDiagnosisError):
            checker.file_reference(self.file, dict(self.reference, bytes=True))

    def test_substituted_file_path(self):
        other = self.root / 'other'
        other.write_bytes(self.file.read_bytes())
        with self.assertRaises(checker.BoundedDiagnosisError):
            checker.file_reference(self.file, self.ref(other))

    def test_reference_fields_are_exact(self):
        with self.assertRaises(checker.BoundedDiagnosisError):
            checker.file_reference(self.file, dict(self.reference, accepted=True))

    def test_owned_reference(self):
        self.assertEqual(self.bundle.reference(self.capture['complete_sidecar'])['sha256'],
                         self.reference['sha256'])

    def test_unknown_alias(self):
        with self.assertRaises(checker.BoundedDiagnosisError):
            self.bundle.reference({'artifact': '#/artifacts/other'})

    def test_reference_does_not_accept_raw_path_or_extra_claim(self):
        for value in [self.reference, {'artifact': '#/artifacts/artifact-00000001', 'complete': True}]:
            with self.subTest(value=value), self.assertRaises(checker.BoundedDiagnosisError):
                self.bundle.reference(value)

    def test_owned_raw_snapshot_needs_no_invented_session_field(self):
        self.bundle.check_capture(self.capture, self.bundle.session)
        self.assertNotIn('session_id', self.capture)

    def test_equal_detached_snapshot_is_not_owned(self):
        with self.assertRaises(checker.BoundedDiagnosisError):
            self.bundle.check_capture(copy.deepcopy(self.capture), self.bundle.session)

    def test_foreign_session(self):
        with self.assertRaises(checker.BoundedDiagnosisError):
            self.bundle.check_capture(self.capture, 'another-session')

    def test_printed_text_cannot_be_promoted_to_complete(self):
        self.capture['completeness']['printed_terms'] = 'complete'
        with self.assertRaises(checker.BoundedDiagnosisError):
            self.bundle.check_capture(self.capture, self.bundle.session)

    def test_identical_full_serialization_and_state_ids(self):
        self.assertTrue(self.bundle.same_state(self.capture, self.capture))

    def test_identical_bounded_text_does_not_prove_same_terms(self):
        other = self.root / 'other.marshal'
        other.write_bytes(b'a different complete serialization')
        self.bundle.aliases['artifact-00000002'] = dict(self.ref(other), path=other.name)
        second = copy.deepcopy(self.capture)
        second['complete_sidecar'] = {'artifact': '#/artifacts/artifact-00000002'}
        self.bundle.owned_captures[id(second)] = second
        self.assertEqual(second['goal'], self.capture['goal'])
        self.assertFalse(self.bundle.same_state(self.capture, second))

    def test_fresh_counter_changes_state_key(self):
        second = copy.deepcopy(self.capture)
        second['fresh_evar_counter'] += 1
        self.bundle.owned_captures[id(second)] = second
        self.assertFalse(self.bundle.same_state(self.capture, second))

    def test_exact_goal_order_changes_state_key(self):
        second = copy.deepcopy(self.capture)
        second['current_goals'] = [{'id': 2}, {'id': 1}]
        self.bundle.owned_captures[id(second)] = second
        self.assertFalse(self.bundle.same_state(self.capture, second))

    def test_legacy_globals_stay_unchanged(self):
        names = ('snapshot', 'command_observation', 'semantic_violations', 'check_capture', 'same_state')
        before = {name: getattr(checker.legacy, name) for name in names}
        self.bundle.trace_path = self.root / 'TRACE.json'
        self.bundle.document = {'schema_version': 1, 'session': {'id': self.bundle.session},
                                'completion': {'trace_complete': False}}
        self.assertTrue(self.bundle.semantic_violations([], self.root))
        self.assertTrue(all(getattr(checker.legacy, name) is value for name, value in before.items()))


if __name__ == '__main__':
    unittest.main()
