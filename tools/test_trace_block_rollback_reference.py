"""Check exact rollback-reference identities with synthetic event envelopes."""
from copy import deepcopy
import hashlib
import json
from pathlib import Path
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).parent / 'block'))
from trace_block_filtered_events import EventFiles
from trace_block_rollback_reference import REUSE_FLAGS, resolve_rollback_references


class CheckedCapture:
    """A test double for a previously validated direct capture."""
    def __init__(self, reference, envelope, process):
        self.capture = {'event_sequence': 2}
        self.catalog = {'schema': 1, 'entries': []}
        self.event_reference = reference
        self.capture_envelope = envelope
        self.owned_process = process

    def stable(self):
        return {'state': 'synthetic checked source'}


class RollbackReferenceTests(unittest.TestCase):
    def run_case(self, edit=None, checked_edit=None, absent=False):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory); process = {'pid': 100, 'start_ticks': 200}
            envelope = {'encoding': 'json-chunks-v1', 'logical_bytes': 10,
                        'root': {'path': 'chunks/source.json', 'sha256': 'a' * 64, 'bytes': 10}}
            source = {'schema': 2, 'sequence': 2, 'kind': 'native-entry', 'rule': 'Control.rule',
                      'invocation': 1, 'trial': False, 'parent_invocation': None, 'capture': envelope}
            def save(row):
                path = root / ('events/process-100/event-%08d.json' % row['sequence'])
                path.parent.mkdir(parents=True, exist_ok=True)
                payload = json.dumps(row, sort_keys=True).encode(); path.write_bytes(payload)
                return {'path': path.relative_to(root).as_posix(), 'sha256': hashlib.sha256(payload).hexdigest()}
            source_reference = save(source)
            event = {'schema': 2, 'sequence': 4, 'kind': 'hand-rollback', 'rule': source['rule'],
                     'invocation': 1, 'trial': False, 'parent_invocation': None, 'clause': 'whole-rule',
                     'exact': True, 'capture_ref': {'event': dict(source_reference,
                         bytes=(root / source_reference['path']).stat().st_size),
                         'source_sequence': 2, 'capture': deepcopy(envelope)},
                     'reuse_check': dict.fromkeys(REUSE_FLAGS, True)}
            event['reuse_check']['kind'] = 'discarded-branch-rollback'
            if edit: edit(source, event)
            # A changed source stays independently sealed. Its old reference in
            # capture_ref must still match the new exact file identity.
            current_source = save(source)
            reference = save(event)
            events = EventFiles(root, [current_source, reference], process)
            checked = CheckedCapture(deepcopy(current_source), deepcopy(source.get('capture')), deepcopy(process))
            if checked_edit: checked_edit(checked)
            captures = resolve_rollback_references(events, {} if absent else {2: checked})
            return captures, checked, reference, source_reference

    def test_exact_prior_capture_retains_both_identities(self):
        captures, source, current, original = self.run_case()
        self.assertIs(captures[2], source)
        self.assertIs(captures[4].capture, source.capture)
        self.assertEqual(captures[4].capture['event_sequence'], 2)
        stable = captures[4].stable()
        self.assertEqual(stable['capture_provenance']['event'], current)
        self.assertEqual(stable['capture_provenance']['event_sequence'], 4)
        self.assertEqual(stable['capture_provenance']['source_sequence'], 2)
        self.assertEqual(stable['capture_provenance']['source_event']['path'], original['path'])
        self.assertNotIn('capture_provenance', source.stable())

    def reject(self, edit):
        with self.assertRaises(ValueError): self.run_case(edit)

    def test_accepted_state_reference_rejects(self):
        self.reject(lambda s, e: e.update(kind='hand-accepted'))

    def test_trial_reference_rejects(self):
        self.reject(lambda s, e: e.update(trial=True))

    def test_direct_and_reference_payload_rejects(self):
        self.reject(lambda s, e: e.update(capture=deepcopy(s['capture'])))

    def test_unknown_event_field_rejects(self):
        self.reject(lambda s, e: e.update(extra=True))

    def test_wrong_invocation_rejects(self):
        self.reject(lambda s, e: e.update(invocation=2))

    def test_wrong_client_rejects(self):
        self.reject(lambda s, e: e.update(rule='Control.foreign'))

    def test_wrong_parent_rejects(self):
        self.reject(lambda s, e: e.update(parent_invocation=7))

    def test_nonprior_source_rejects(self):
        self.reject(lambda s, e: e['capture_ref'].update(source_sequence=4))

    def test_boolean_source_sequence_rejects(self):
        self.reject(lambda s, e: e['capture_ref'].update(source_sequence=True))

    def test_wrong_source_size_rejects(self):
        self.reject(lambda s, e: e['capture_ref']['event'].update(bytes=1))

    def test_wrong_source_hash_rejects(self):
        self.reject(lambda s, e: e['capture_ref']['event'].update(sha256='b' * 64))

    def test_foreign_process_reference_rejects(self):
        self.reject(lambda s, e: e['capture_ref']['event'].update(path='events/process-999/event-00000002.json'))

    def test_changed_envelope_rejects(self):
        self.reject(lambda s, e: e['capture_ref']['capture']['root'].update(sha256='b' * 64))

    def test_missing_reuse_check_rejects(self):
        self.reject(lambda s, e: e['reuse_check'].pop('evd_physical_equal'))

    def test_false_reuse_check_rejects(self):
        self.reject(lambda s, e: e['reuse_check'].update(environment_physical_equal=False))

    def test_integer_reuse_flag_rejects(self):
        self.reject(lambda s, e: e['reuse_check'].update(exact=1))

    def test_unknown_reuse_flag_rejects(self):
        self.reject(lambda s, e: e['reuse_check'].update(extra=True))

    def test_alias_chain_rejects(self):
        self.reject(lambda s, e: s.update(capture_ref=deepcopy(e['capture_ref'])))

    def test_unchecked_capture_rejects(self):
        with self.assertRaises(ValueError): self.run_case(absent=True)

    def test_wrong_checked_source_reference_rejects(self):
        with self.assertRaises(ValueError):
            self.run_case(checked_edit=lambda c: c.event_reference.update(sha256='f' * 64))

    def test_wrong_checked_source_envelope_rejects(self):
        with self.assertRaises(ValueError):
            self.run_case(checked_edit=lambda c: c.capture_envelope.update(logical_bytes=11))

    def test_wrong_checked_process_rejects(self):
        with self.assertRaises(ValueError):
            self.run_case(checked_edit=lambda c: c.owned_process.update(start_ticks=999))

    def test_original_source_sequence_remains_required(self):
        with self.assertRaises(ValueError):
            self.run_case(checked_edit=lambda c: c.capture.update(event_sequence=4))


if __name__ == '__main__':
    unittest.main()
