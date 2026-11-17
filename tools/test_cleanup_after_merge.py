"""Check the merge cleanup script against a temporary repository and build tree."""

import json
import os
from pathlib import Path
import subprocess
import tempfile
import unittest

SCRIPT = Path(__file__).resolve().parent / 'cleanup_after_merge.sh'


class CleanupAfterMerge(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name) / 'repo'
        self.root.mkdir()
        self.environment = dict(os.environ, GIT_AUTHOR_NAME='t', GIT_AUTHOR_EMAIL='t@t',
                                GIT_COMMITTER_NAME='t', GIT_COMMITTER_EMAIL='t@t')
        self.environment.pop('ZESU_MAIN_REF', None)
        self.git('init', '-q', '-b', 'main')
        (self.root / '.gitignore').write_text('/_build/\n/.worktrees/\n__pycache__/\n')
        self.git('add', '.gitignore')
        self.git('commit', '-q', '-m', 'base')
        self.origin = Path(self.temp.name) / 'origin.git'
        self.git('init', '-q', '--bare', '-b', 'main', str(self.origin))
        self.git('remote', 'add', 'origin', str(self.origin))
        self.git('push', '-q', 'origin', 'main')
        self.worktree = self.root / '.worktrees/feature'
        self.git('worktree', 'add', '-q', str(self.worktree), '-b', 'w/feature')
        (self.worktree / 'feature.txt').write_text('feature\n')
        self.git('add', 'feature.txt', cwd=self.worktree)
        self.git('commit', '-q', '-m', 'feature', cwd=self.worktree)

    def git(self, *arguments, cwd=None):
        return subprocess.run(['git', '-C', str(cwd or self.root), *arguments], check=True,
                              capture_output=True, text=True, env=self.environment).stdout

    def merge(self):
        """Merge on the remote, as GitHub does: the local origin/main stays at the old main."""
        base = self.git('rev-parse', 'main').strip()
        self.git('merge', '-q', '--no-ff', '-m', 'merge', 'w/feature')
        self.git('push', '-q', 'origin', 'main')
        self.git('update-ref', 'refs/remotes/origin/main', base)
        self.git('reset', '-q', '--hard', base)

    def test_merge_seen_only_on_origin_is_fetched(self):
        self.merge()
        tied = self.item('a/run1', 'w/feature')
        result = self.cleanup('w/feature')
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertFalse(self.worktree.exists())
        self.assertFalse(tied.exists())
        self.assertEqual(self.git('rev-parse', 'origin/main'), self.git('--git-dir', str(self.origin),
                                                                        'rev-parse', 'main'))

    def test_failed_fetch_stops_before_deciding(self):
        self.merge()
        self.git('remote', 'set-url', 'origin', str(Path(self.temp.name) / 'missing.git'))
        tied = self.item('a/run1', 'w/feature')
        result = self.cleanup('w/feature')
        self.assertEqual(result.returncode, 2)
        self.assertIn('git fetch origin failed', result.stderr)
        self.assertTrue(self.worktree.exists())
        self.assertTrue(tied.exists())

    def item(self, relative, branch=None):
        path = self.root / '_build/agents' / relative
        path.mkdir(parents=True)
        (path / 'Module.vo').write_bytes(b'object')
        if branch:
            (path / 'ITEM.json').write_text(json.dumps({'branch': branch}))
        return path

    def cleanup(self, *arguments):
        return subprocess.run([str(SCRIPT), *arguments], cwd=self.root, capture_output=True,
                              text=True, env=self.environment, timeout=60)

    def test_merged_branch_loses_clean_worktree_and_its_run_dirs(self):
        self.merge()
        tied = self.item('a/run1', 'w/feature')
        named = self.item('b/feature')
        foreign = self.item('b/other', 'other')
        orch = self.item('orch/w-feature')
        result = self.cleanup('w/feature')
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertFalse(self.worktree.exists())
        self.assertFalse(tied.exists())
        self.assertFalse(named.exists())
        self.assertTrue(foreign.exists())
        self.assertTrue(orch.exists())
        self.assertIn('removed worktree', result.stdout)
        self.assertIn('removed run dir ' + str(tied), result.stdout)
        self.assertIn('kept: protected agent', result.stdout)
        self.assertIn('w/feature', self.git('branch', '--list', 'w/feature'))
        self.assertIn(str(tied), (self.root / '_build/janitor/janitor.log').read_text())

    def test_run_from_inside_the_removed_worktree_completes(self):
        # 2026-11-15: run from the branch's own worktree, the script removed that
        # worktree and then failed to find tools/build_janitor.py (exit 1).
        tools = self.worktree / 'tools'
        tools.mkdir()
        for name in ('cleanup_after_merge.sh', 'build_janitor.py', 'goal_store.py'):
            (tools / name).write_bytes((SCRIPT.parent / name).read_bytes())
            (tools / name).chmod((SCRIPT.parent / name).stat().st_mode & 0o777)
        self.git('add', 'tools', cwd=self.worktree)
        self.git('commit', '-q', '-m', 'tools', cwd=self.worktree)
        self.merge()
        tied = self.item('a/run1', 'w/feature')
        temporary = Path(self.temp.name) / 'tmp'
        temporary.mkdir()
        result = subprocess.run([str(tools / 'cleanup_after_merge.sh'), 'w/feature'], cwd=self.worktree,
                                capture_output=True, text=True, timeout=60,
                                env=dict(self.environment, TMPDIR=str(temporary)))
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIn('removed worktree ' + str(self.worktree), result.stdout)
        self.assertFalse(self.worktree.exists())
        self.assertFalse(tied.exists())
        self.assertEqual(list(temporary.iterdir()), [])

    def test_saved_goals_of_a_cleaned_branch_stay_in_the_store(self):
        # 2026-11-15: cleanup deleted 0300's probe dir with its saved residual goals.
        self.merge()
        tied = self.item('a/probe0300', 'w/feature')
        (tied / 'goals').mkdir()
        (tied / 'goals/Goal1.v').write_text('Lemma tg_goal_1 : True.\n')
        (tied / 'goals/state.json').write_text('{}')
        (tied / 'ProbeGoal0.v').write_text('Lemma probe : True.\n')
        (tied / 'default').mkdir()
        (tied / 'default/GoalDomain.v').write_text('(* build copy *)\n')
        built = self.worktree / '_build/scratch'
        built.mkdir(parents=True)
        (built / 'Goal7.v').write_text('Lemma seven : True.\n')
        result = self.cleanup('w/feature')
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertFalse(tied.exists())
        self.assertFalse(self.worktree.exists())
        store = self.root / '_build/goals/_rescued'
        [run] = (store / 'a-probe0300').iterdir()
        self.assertEqual((run / 'goals/Goal1.v').read_text(), 'Lemma tg_goal_1 : True.\n')
        self.assertTrue((run / 'ProbeGoal0.v').exists())
        self.assertFalse((run / 'goals/state.json').exists())
        self.assertFalse((run / 'default').exists())
        manifest = json.loads((run / 'MANIFEST.json').read_text())
        self.assertEqual(manifest['branch'], 'w/feature')
        self.assertEqual(manifest['rescued_from'], str(tied))
        self.assertEqual(sorted(e['name'] for e in manifest['files']),
                         ['ProbeGoal0.v', 'goals/Goal1.v'])
        [worktree_run] = (store / 'feature').iterdir()
        self.assertTrue((worktree_run / 'scratch/Goal7.v').exists())
        self.assertIn('saved 2 goal file(s) from ' + str(tied), result.stdout)
        self.assertIn('saved goals from ' + str(tied),
                      (self.root / '_build/janitor/janitor.log').read_text())

    def test_closure_records_of_a_cleaned_branch_are_kept(self):
        self.merge()
        tied = self.item('a/sweep1', 'w/feature')
        (tied / '0300').mkdir()
        (tied / '0300/CLOSURE.json').write_text('{"case": "0300", "verdict": "CLOSED"}\n')
        (tied / '0514').mkdir()
        (tied / '0514/NOT-CLOSED.json').write_text('{"case": "0514", "verdict": "NOT-CLOSED"}\n')
        (tied / 'ITEM.json').write_text(json.dumps({'branch': 'w/feature',
                                                    'function': 'decodeItem'}))
        dry = self.cleanup('--dry-run', 'w/feature')
        self.assertIn('would save closure record ' + str(tied / '0300/CLOSURE.json'), dry.stdout)
        result = self.cleanup('w/feature')
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertFalse(tied.exists())
        store = self.root / '_build/closures/decodeItem'
        self.assertEqual((store / '0300/a-sweep1/CLOSURE.json').read_text(),
                         '{"case": "0300", "verdict": "CLOSED"}\n')
        self.assertTrue((store / '0514/a-sweep1/NOT-CLOSED.json').exists())
        self.assertIn('saved 2 closure record(s) from ' + str(tied), result.stdout)

    def test_cleanup_never_deletes_the_store(self):
        self.merge()
        stored = self.root / '_build/goals/decodeItem/0300/lia-1/Goal1.v'
        stored.parent.mkdir(parents=True)
        stored.write_text('Lemma g : True.\n')
        self.item('a/goals', 'w/feature')
        result = self.cleanup('w/feature')
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertTrue(stored.exists())

    def test_long_worktree_list_does_not_stop_the_lookup(self):
        # The base checkout has hundreds of worktrees. A lookup that stops reading
        # early kills `git worktree list` with SIGPIPE, and pipefail ended the script.
        self.merge()
        tied = self.item('a/run1', 'w/feature')
        nested = Path(*(['x' * 200] * 15))
        for index in range(40):
            self.git('worktree', 'add', '-q', '--detach', '--no-checkout',
                     str(self.root / '.worktrees' / nested / f'filler-{index:02d}'))
        listing = self.git('worktree', 'list', '--porcelain')
        self.assertGreater(len(listing) - listing.index(str(self.worktree)), 1 << 16)
        result = self.cleanup('w/feature')
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertFalse(self.worktree.exists())
        self.assertFalse(tied.exists())
        self.assertIn('removed worktree ' + str(self.worktree), result.stdout)

    def test_dirty_worktree_stays(self):
        self.merge()
        (self.worktree / 'notes.txt').write_text('untracked\n')
        result = self.cleanup('w/feature')
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertTrue((self.worktree / 'notes.txt').exists())
        self.assertIn('uncommitted or untracked', result.stdout)

    def test_unmerged_branch_changes_nothing(self):
        self.git('update-ref', 'refs/remotes/origin/main', 'main')
        tied = self.item('a/run1', 'w/feature')
        result = self.cleanup('w/feature')
        self.assertEqual(result.returncode, 3)
        self.assertIn('not merged', result.stderr)
        self.assertTrue(self.worktree.exists())
        self.assertTrue(tied.exists())

    def test_dry_run_reports_without_deleting(self):
        self.merge()
        tied = self.item('a/run1', 'w/feature')
        result = self.cleanup('--dry-run', 'w/feature')
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertTrue(self.worktree.exists())
        self.assertTrue(tied.exists())
        self.assertIn('would remove worktree', result.stdout)
        self.assertIn('would remove run dir', result.stdout)

    def test_dry_run_names_the_goals_it_would_save(self):
        self.merge()
        tied = self.item('a/run1', 'w/feature')
        (tied / 'Goal3.v').write_text('Lemma g : True.\n')
        result = self.cleanup('--dry-run', 'w/feature')
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIn('would save goal ' + str(tied / 'Goal3.v'), result.stdout)
        self.assertFalse((self.root / '_build/goals').exists())

    def test_main_is_refused(self):
        result = self.cleanup('main')
        self.assertEqual(result.returncode, 2)


if __name__ == '__main__':
    unittest.main()
