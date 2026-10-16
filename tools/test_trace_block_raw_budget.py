"""Check final budget records without executing a producer or native proof."""
from copy import deepcopy
import hashlib
import json
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).parent / 'block'))
from trace_block_raw_budget_validation import (RAW_LIMIT_BYTES, LEDGER_BYTES, CONTROL_RESERVE_BYTES,
    LEDGER_PATH, validate_ledger, verify_raw_budget)


class RawBudgetTests(unittest.TestCase):
    def ledger(self, root, denied=False):
        return {'schema': 1, 'root': str(root), 'limit_bytes': RAW_LIMIT_BYTES,
                'control_reserve_bytes': CONTROL_RESERVE_BYTES, 'used_bytes': LEDGER_BYTES + 4,
                'complete': not denied, 'denied_writes': int(denied),
                'first_denial': {'path': 'evidence/large.marshal', 'requested_bytes': RAW_LIMIT_BYTES,
                                 'channel': 'data'} if denied else None}

    def run_case(self, *, denied=False, edit=None, session=True, sealed_session=True, supplied_edit=None,
                 after_seal=None, after_verify=None):
        with tempfile.TemporaryDirectory() as temporary:
            outer = Path(temporary); root = outer / 'raw'; (root / 'evidence').mkdir(parents=True)
            ledger = self.ledger(root, denied)
            status = {'complete': not denied, 'raw_budget': {'schema': 1,
                      'limit_bytes': RAW_LIMIT_BYTES, 'limit_reached': denied, 'ledger': LEDGER_PATH}}
            record = {'raw_budget': {'ledger_path': LEDGER_PATH, 'limit_bytes': RAW_LIMIT_BYTES,
                                    'complete': not denied}, 'observer_status': {'status': status}}
            config = {'ledger': ledger, 'session': record if session else None}
            if edit: edit(config)
            if session and sealed_session:
                (root / 'evidence/SESSION.json').write_text(json.dumps(config['session'], sort_keys=True))
                ledger['used_bytes'] += (root / 'evidence/SESSION.json').stat().st_size
            if supplied_edit and config['session'] is not None:
                config['session'] = deepcopy(config['session']); supplied_edit(config['session'])
            raw = json.dumps(ledger, sort_keys=True).encode()
            (root / LEDGER_PATH).write_bytes(raw + b' ' * (LEDGER_BYTES - len(raw) - 1) + b'\n')
            (root / 'evidence/data').write_bytes(b'data')
            rows = []
            for path in sorted(root.rglob('*')):
                if path.is_file():
                    content = path.read_bytes()
                    rows.append({'path': path.relative_to(root).as_posix(),
                                 'sha256': hashlib.sha256(content).hexdigest(), 'bytes': len(content)})
            seal = outer / 'SEAL.json'
            seal.write_text(json.dumps({'schema_version': 1, 'root': str(root),
                                       'session_id': 'synthetic', 'files': rows}))
            reference = {'path': str(seal), 'sha256': hashlib.sha256(seal.read_bytes()).hexdigest()}
            if after_seal: after_seal(root)
            if after_verify:
                from trace_block_seal import verify_root_seal
                def swapped(*args):
                    result = verify_root_seal(*args); after_verify(root); return result
                with patch('trace_block_seal.verify_root_seal', side_effect=swapped):
                    return verify_raw_budget(root, config['session'], reference)
            return verify_raw_budget(root, config['session'], reference)

    def reject(self, edit, *, denied=False):
        with self.assertRaises((ValueError, KeyError)):
            self.run_case(edit=edit, denied=denied)

    def test_complete_budget_is_not_a_proof_claim(self):
        result = self.run_case()
        self.assertTrue(result['complete'])
        self.assertGreater(result['actual_bytes'], LEDGER_BYTES + 4)
        self.assertEqual(result['session']['path'], 'evidence/SESSION.json')
        self.assertFalse(result['limit_reached'])
        self.assertIn('does not establish', result['coverage_limit'])

    def test_denial_blocks_completeness(self):
        result = self.run_case(denied=True)
        self.assertFalse(result['complete'])
        self.assertTrue(result['limit_reached'])

    def test_missing_session_stays_incomplete(self):
        self.assertFalse(self.run_case(session=False)['complete'])

    def test_missing_status_stays_incomplete(self):
        self.assertFalse(self.run_case(edit=lambda c: c['session'].update(observer_status=None))['complete'])

    def test_wrong_root_rejects(self):
        self.reject(lambda c: c['ledger'].update(root='/foreign'))

    def test_wrong_limit_rejects(self):
        self.reject(lambda c: c['ledger'].update(limit_bytes=RAW_LIMIT_BYTES + 1))

    def test_boolean_counter_rejects(self):
        self.reject(lambda c: c['ledger'].update(denied_writes=False))

    def test_actual_bytes_exceed_reservation_rejects(self):
        self.reject(lambda c: c['ledger'].update(used_bytes=LEDGER_BYTES))

    def test_reservation_exceeds_ceiling_rejects(self):
        self.reject(lambda c: c['ledger'].update(used_bytes=RAW_LIMIT_BYTES + 1))

    def test_ledger_unknown_fields_reject(self):
        self.reject(lambda c: c['ledger'].update(extra=True))

    def test_missing_denial_rejects(self):
        self.reject(lambda c: c['ledger'].update(first_denial=None), denied=True)

    def test_unsafe_denial_rejects(self):
        self.reject(lambda c: c['ledger']['first_denial'].update(path='../foreign'), denied=True)

    def test_denial_channel_rejects(self):
        self.reject(lambda c: c['ledger']['first_denial'].update(channel='stdout'), denied=True)

    def test_session_hash_substitution_rejects(self):
        self.reject(lambda c: c['session']['raw_budget'].update(sha256='a' * 64))

    def test_session_flag_substitution_rejects(self):
        self.reject(lambda c: c['session']['raw_budget'].update(complete=True), denied=True)

    def test_observer_flag_substitution_rejects(self):
        self.reject(lambda c: c['session']['observer_status']['status']['raw_budget'].update(limit_reached=False), denied=True)

    def test_observer_complete_after_denial_rejects(self):
        self.reject(lambda c: c['session']['observer_status']['status'].update(complete=True), denied=True)

    def test_ledger_layout_has_exact_size(self):
        self.assertEqual(self.run_case()['ledger']['bytes'], 8192)

    def test_actual_count_over_ceiling_rejects(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            with self.assertRaises(ValueError):
                validate_ledger(self.ledger(root), root, RAW_LIMIT_BYTES + 1)

    def test_supplied_session_without_sealed_file_rejects(self):
        with self.assertRaises(ValueError): self.run_case(sealed_session=False)

    def test_supplied_session_substitution_rejects(self):
        with self.assertRaises(ValueError):
            self.run_case(supplied_edit=lambda s: s.update(foreign_session=True))

    def test_supplied_complete_flag_substitution_rejects(self):
        with self.assertRaises(ValueError):
            self.run_case(denied=True, supplied_edit=lambda s: s['raw_budget'].update(complete=True))

    def test_supplied_boolean_integer_substitution_rejects(self):
        def add_state(config): config['session']['final_state_id'] = 1
        with self.assertRaises(ValueError):
            self.run_case(edit=add_state, supplied_edit=lambda s: s.update(final_state_id=True))

    def test_external_directory_symlink_rejects_before_filtering(self):
        def link(root):
            outside = root.parent / 'outside'; outside.mkdir(); (outside / 'unsealed').write_text('data')
            (root / 'evidence/external').symlink_to(outside, target_is_directory=True)
        with self.assertRaises(ValueError): self.run_case(after_seal=link)

    def test_broken_link_rejects_before_filtering(self):
        with self.assertRaises(ValueError):
            self.run_case(after_seal=lambda root: (root / 'evidence/broken').symlink_to('absent'))

    def test_same_bytes_external_file_link_rejects(self):
        def link(root):
            outside = root.parent / 'outside'; outside.write_bytes(b'data')
            data = root / 'evidence/data'; data.unlink(); data.symlink_to(outside)
        with self.assertRaises(ValueError): self.run_case(after_seal=link)

    def test_denied_ledger_replacement_rejects(self):
        def complete_session(config):
            record = config['session']; record['raw_budget']['complete'] = True
            status = record['observer_status']['status']; status['complete'] = True
            status['raw_budget']['limit_reached'] = False
        def replace(root):
            path = root / LEDGER_PATH; value = json.loads(path.read_text())
            value.update(complete=True, denied_writes=0, first_denial=None)
            payload = json.dumps(value, sort_keys=True).encode()
            path.write_bytes(payload + b' ' * (LEDGER_BYTES - len(payload) - 1) + b'\n')
        with self.assertRaisesRegex(ValueError, 'parsed ledger bytes'):
            self.run_case(denied=True, edit=complete_session, after_verify=replace)

    def test_session_replacement_after_verification_rejects(self):
        def replace(root):
            path = root / 'evidence/SESSION.json'; value = json.loads(path.read_text())
            value['foreign_session'] = True; path.write_text(json.dumps(value, sort_keys=True))
        with self.assertRaisesRegex(ValueError, 'parsed SESSION bytes'):
            self.run_case(supplied_edit=lambda s: s.update(foreign_session=True), after_verify=replace)


if __name__ == '__main__':
    unittest.main()
