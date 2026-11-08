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
        (self.root / '.gitignore').write_text('/_build/\n/.worktrees/\n')
        self.git('add', '.gitignore')
        self.git('commit', '-q', '-m', 'base')
        self.worktree = self.root / '.worktrees/feature'
        self.git('worktree', 'add', '-q', str(self.worktree), '-b', 'w/feature')
        (self.worktree / 'feature.txt').write_text('feature\n')
        self.git('add', 'feature.txt', cwd=self.worktree)
        self.git('commit', '-q', '-m', 'feature', cwd=self.worktree)

    def git(self, *arguments, cwd=None):
        return subprocess.run(['git', '-C', str(cwd or self.root), *arguments], check=True,
                              capture_output=True, text=True, env=self.environment).stdout

    def merge(self):
        self.git('merge', '-q', '--no-ff', '-m', 'merge', 'w/feature')
        self.git('update-ref', 'refs/remotes/origin/main', 'main')

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

    def test_main_is_refused(self):
        result = self.cleanup('main')
        self.assertEqual(result.returncode, 2)


if __name__ == '__main__':
    unittest.main()
