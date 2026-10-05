"""Complete bytes and exact residuals survive evidence compaction."""
import hashlib
import json
from pathlib import Path
import sys
import tempfile
import unittest
sys.path.insert(0, str(Path(__file__).resolve().parent / 'block'))
from archive_discovery import store, bounded_report, diagnose_capture


class ArchiveDiscoveryTests(unittest.TestCase):
    def test_archive_retains_original_bytes_and_deduplicates(self):
        with tempfile.TemporaryDirectory() as root:
            data = b'feedback\x00\n'
            first = store(root, data)
            self.assertEqual(first, store(root, data))
            self.assertEqual(Path(first['archive_path']).read_bytes(), data)
            self.assertEqual(first['sha256'], hashlib.sha256(data).hexdigest())

    def test_compaction_preserves_first_goal_and_debts(self):
        goal = {'conclusion': 'FindRegMapsTo x14', 'spatial': ['owned'], 'context': 'complete context'}
        capture = {'outcome': 'stalled', 'pending_goals': [goal], 'shelved_goals': [goal],
                   'inherited_debts': ['old debt'], 'feedback': 'bulk feedback'}
        report = {'classes': {'contract-gap': 1}, 'blocks': [
            {'entry': '0x10', 'first_residual': goal, 'captures': [capture]}]}
        with tempfile.TemporaryDirectory() as root:
            bounded = bounded_report(report, {}, root)
            row = bounded['blocks'][0]
            self.assertEqual(row['first_residual']['conclusion'], goal['conclusion'])
            restored = json.loads(Path(row['first_residual']['full_goal']['archive_path']).read_text())
            self.assertEqual(restored, goal)
            record = row['captures'][0]
            self.assertEqual(record['inherited_debts'], ['old debt'])
            self.assertEqual(record['shelved_goal_count'], 1)
            self.assertEqual(json.loads(Path(record['full_capture']['archive_path']).read_text()), capture)
            self.assertEqual(report['blocks'][0]['first_residual'], goal)

    def test_query_timeout_is_not_a_proof_search(self):
        result = diagnose_capture({'outcome': 'setup-error', 'proof_phase_entered': False},
                                  [{'success': False, 'reason': 'timeout', 'pet_restarted': True}])
        self.assertEqual(result['outcome'], 'setup-timeout')
        self.assertFalse(result['search_failure']['proof_execution'])
        self.assertNotIn('last_valid_goals', result)

    def test_tactic_timeout_retains_the_last_valid_goal(self):
        result = diagnose_capture({'outcome': 'mcp-error', 'proof_phase_entered': True},
                                  [{'success': False, 'reason': 'tactic_failed', 'error': 'Coq: Timeout!',
                                    'failed_command': 'try zesu_block.', 'goals_at_failure': 'entry goal'}])
        self.assertEqual(result['outcome'], 'automation-search-timeout')
        self.assertEqual(result['last_valid_goals'], 'entry goal')
        self.assertFalse(result['search_failure']['progressed_residual_available'])

    def test_other_setup_errors_retain_their_class(self):
        result = diagnose_capture({'outcome': 'setup-error', 'proof_phase_entered': False},
                                  [{'success': False, 'reason': 'invalid_name'}])
        self.assertEqual(result['outcome'], 'setup-error')

    def test_abstract_stop_does_not_become_a_closed_contract(self):
        result = diagnose_capture({'outcome': 'reached', 'proof_phase_entered': True}, [])
        self.assertEqual(result['outcome'], 'abstract-successor-reached')
        self.assertEqual(result['raw_outcome'], 'reached')

    def test_conflicting_archive_is_rejected(self):
        with tempfile.TemporaryDirectory() as root:
            entry = store(root, b'original')
            Path(entry['archive_path']).write_bytes(b'changed')
            with self.assertRaisesRegex(ValueError, 'conflicting'):
                store(root, b'original')


if __name__ == '__main__':
    unittest.main()
