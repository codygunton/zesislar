"""Check timing and goal retention without changing primary classification."""
import sys
import unittest
from pathlib import Path
sys.path.insert(0, str(Path(__file__).parent/'block'))
from native_diagnostics import goal_size, is_primary_timeout, timed_result


class NativeDiagnosticTests(unittest.TestCase):
    def test_goal_size_counts_utf8_bytes_without_discarding_variables(self):
        goals = 'x : Z\n|- P ∗ Q'
        result = goal_size(goals)
        self.assertEqual(result['utf8_bytes'], len(goals.encode()))
        self.assertEqual(result['lines'], 2)
        self.assertTrue(result['available'])
        self.assertNotEqual(result['sha256'], goal_size('|- P ∗ Q')['sha256'])

    def test_absent_goals_are_not_empty_goals(self):
        self.assertFalse(goal_size(None)['available'])
        self.assertTrue(goal_size('')['available'])
        self.assertEqual(goal_size('')['utf8_bytes'], 0)

    def test_only_primary_coq_tactic_timeout_triggers_secondary_pass(self):
        failure = {'success': False, 'error': 'Coq: Timeout!', 'reason': 'tactic_failed'}
        self.assertTrue(is_primary_timeout([failure]))
        self.assertFalse(is_primary_timeout([{'success': False, 'reason': 'timeout'}]))
        self.assertFalse(is_primary_timeout([{'success': False, 'error': 'Coq: Timeout!', 'reason': 'unavailable'}]))

    def test_failed_transaction_preserves_measured_input_goal(self):
        import time
        row = timed_result('primary', time.monotonic(), '2026-10-05T00:00:00Z',
                           'x : Z\n|- P', {'success': False, 'error': 'Coq: Timeout!'})
        self.assertEqual(row['goals_before'], goal_size('x : Z\n|- P'))
        self.assertFalse(row['goals_after']['available'])
        self.assertGreaterEqual(row['elapsed_seconds'], 0)


if __name__ == '__main__':
    unittest.main()
