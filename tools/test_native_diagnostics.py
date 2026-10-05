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


class FocusSelectorTests(unittest.TestCase):
    def test_native_step_focuses_one_goal_and_retains_all_returned_goals(self):
        import asyncio
        from types import SimpleNamespace
        from native_diagnostics import native_step
        goals = 'Goal 1: |- first\nGoal 2: |- second'
        result = {'success': True, 'state_id': 12, 'from_state_id': 11,
                  'goals': 'Goal 1: |- first_next\nGoal 2: |- second',
                  'shelved_goals': ['inherited debt']}
        class Session:
            async def call_tool(self, name, arguments):
                if arguments['body'] != '1: zesu_liAStep.':
                    raise RuntimeError('Expected a single focused goal but 2 goals are focused')
                self.arguments = arguments
                return SimpleNamespace(structuredContent=result)
        session = Session()
        measurements = []
        returned = asyncio.run(native_step(session, {'state_id': 11, 'goals': goals}, 300, measurements))
        self.assertEqual(returned, result)
        self.assertIn('Goal 2: |- second', returned['goals'])
        self.assertEqual(returned['shelved_goals'], ['inherited debt'])
        self.assertEqual(session.arguments['from_state'], 11)
        self.assertEqual(measurements[0]['goals_before'], goal_size(goals))
        self.assertEqual(measurements[0]['goals_after'], goal_size(result['goals']))


if __name__ == '__main__':
    unittest.main()
