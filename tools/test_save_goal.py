"""Check tools/save_goal.py and the goal-store pattern."""

import contextlib
import io
import json
from pathlib import Path
import tempfile
import unittest

import goal_store
import save_goal


class SaveGoal(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.goal = self.root / 'probe/Goal1.v'
        self.goal.parent.mkdir()
        self.goal.write_text('Lemma tg_goal_1 : True.\n')

    def save(self, *extra, files=None):
        output, error = io.StringIO(), io.StringIO()
        with contextlib.redirect_stdout(output), contextlib.redirect_stderr(error):
            status = save_goal.main(['--root', str(self.root), '--function', 'decodeItem',
                                     '--case', '0300', '--tag', 'lia-1', '--head', 'abc',
                                     '--bank', '/banks/abc', '--command', 'make probe', *extra,
                                     *(files or [str(self.goal)])])
        return status, output.getvalue(), error.getvalue()

    def test_copies_the_goal_and_writes_the_manifest(self):
        status, output, error = self.save()
        self.assertEqual(status, 0, error)
        directory = self.root / '_build/goals/decodeItem/0300/lia-1'
        self.assertEqual(output.strip(), str(directory))
        self.assertEqual((directory / 'Goal1.v').read_text(), 'Lemma tg_goal_1 : True.\n')
        self.assertTrue(self.goal.exists())
        manifest = json.loads((directory / 'MANIFEST.json').read_text())
        self.assertEqual((manifest['head'], manifest['bank'], manifest['command']),
                         ('abc', '/banks/abc', 'make probe'))
        self.assertRegex(manifest['date'], r'^\d{4}-\d\d-\d\dT')
        self.assertEqual([entry['name'] for entry in manifest['files']], ['Goal1.v'])

    def test_refuses_large_files_bad_names_and_overwrites(self):
        large = self.root / 'probe/Goal2.v'
        large.write_bytes(b'x' * (goal_store.GOAL_MAX_BYTES + 1))
        self.assertEqual(self.save(files=[str(large)])[0], 1)
        self.assertEqual(self.save()[0], 0)
        self.goal.write_text('Lemma other : True.\n')
        status, _, error = self.save()
        self.assertEqual(status, 1)
        self.assertIn('other content', error)
        output, error = io.StringIO(), io.StringIO()
        with contextlib.redirect_stdout(output), contextlib.redirect_stderr(error):
            status = save_goal.main(['--root', str(self.root), '--function', '../x', '--case',
                                     'c', '--tag', 't', str(self.goal)])
        self.assertEqual(status, 1)

    def test_pattern_matches_lane_outputs_and_skips_build_copies(self):
        self.assertTrue(goal_store.is_goal('goals/Goal3.v'))
        self.assertTrue(goal_store.is_goal('goals/698c-2/G0144post.v'))
        self.assertTrue(goal_store.is_goal('owned005/MeaningDomain426Goal013.v'))
        self.assertFalse(goal_store.is_goal('goals/state.json'))
        self.assertFalse(goal_store.is_goal('Probe.v'))
        self.assertFalse(goal_store.is_goal('default/ZesuSsz/Automation2/GoalDomain.v'))
        self.assertFalse(goal_store.is_goal('bank/default/Goal1.v'))


if __name__ == '__main__':
    unittest.main()
