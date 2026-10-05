"""Complete-goal export retains all raw fields without formatting limits."""
import json
from pathlib import Path
import sys
import tempfile
import unittest
sys.path.insert(0, str(Path(__file__).parent/'block'))
from complete_goals_mcp import write_export


class ExportTests(unittest.TestCase):
    def test_exports_large_goals_and_every_debt_class(self):
        value = {'goals': [{'hyps': [], 'ty': 'x'*70000}],
                 'stack': [[[], [{'ty': 'stack proposition'}]]],
                 'shelf': [{'ty': 'shelved proposition'}],
                 'given_up': [{'ty': 'given-up proposition'}]}
        class Complete:
            def to_json(self):
                return value
        with tempfile.TemporaryDirectory() as root:
            result = write_export(Complete(), root, 12)
            self.assertEqual(json.loads(Path(result['path']).read_text()), value)
            self.assertGreater(result['bytes'], 70000)
            self.assertEqual(result['stack_frame_goal_counts'], [{'left': 0, 'right': 1}])
            self.assertEqual(result['shelved_goals'], 1)
            self.assertEqual(result['given_up_goals'], 1)

    def test_missing_proof_scope_is_unavailable_and_creates_no_goal_payload(self):
        with tempfile.TemporaryDirectory() as root:
            result = write_export(None, root, 19)
            self.assertFalse(result['success'])
            self.assertEqual(result['reason'], 'no-proof-scope')
            self.assertEqual(result['state_id'], 19)
            self.assertEqual(list(Path(root).iterdir()), [])

    def test_rejects_changed_data_for_the_same_live_state(self):
        class Complete:
            def to_json(self):
                return {'goals': [], 'stack': [], 'shelf': [], 'given_up': []}
        with tempfile.TemporaryDirectory() as root:
            write_export(Complete(), root, 12)
            Path(root, 'state_12.json').write_text('changed')
            with self.assertRaisesRegex(ValueError, 'same state'):
                write_export(Complete(), root, 12)


if __name__ == '__main__':
    unittest.main()
