import hashlib
import json
from pathlib import Path
import subprocess
import tempfile
import unittest

from gate_workspace import prepare


class GateWorkspaceTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        root = Path(self.temporary.name)
        self.seed, self.work = root / 'seed', root / 'work'
        self.source = self.seed / '_build/pinned-source'
        self.source.mkdir(parents=True)
        self.work.mkdir()
        self.run_git('init', '-q')
        self.run_git('config', 'user.name', 'Fixture')
        self.run_git('config', 'user.email', 'fixture@example.invalid')
        (self.source / 'source.txt').write_text('pinned\n')
        self.run_git('add', 'source.txt')
        self.run_git('commit', '-qm', 'Pinned source')
        self.record = dict(path='_build/pinned-source',
            commit=self.run_git('rev-parse', 'HEAD'),
            tree=self.run_git('rev-parse', 'HEAD^{tree}'),
            patch_sha256=hashlib.sha256(b'').hexdigest())
        self.recipe = self.work / 'build/stock-zisk/build-recipe.json'
        self.recipe.parent.mkdir(parents=True)
        self.write_recipe()

    def run_git(self, *args):
        return subprocess.check_output(['git', '-C', str(self.source), *args],
                                       text=True).strip()

    def write_recipe(self):
        self.recipe.write_text(json.dumps({'sources': {'fixture': self.record}}))

    def test_prepare_creates_checked_relative_link_and_is_idempotent(self):
        result = prepare(self.work, source_workspace=self.seed)
        target = self.work / self.record['path']
        self.assertEqual(result['created_links'], 1)
        self.assertTrue(target.is_symlink())
        self.assertFalse(target.readlink().is_absolute())
        self.assertEqual(target.resolve(), self.source)
        self.assertEqual(prepare(self.work, source_workspace=self.seed)['created_links'], 0)
        self.assertEqual(prepare(self.work, check_only=True)['created_links'], 0)

    def test_check_missing_checkout_does_not_create_it(self):
        with self.assertRaisesRegex(ValueError, 'missing'):
            prepare(self.work, check_only=True)
        self.assertFalse((self.work / '_build').exists())

    def test_wrong_commit_creates_no_link(self):
        self.record['commit'] = '0' * 40
        self.write_recipe()
        with self.assertRaisesRegex(ValueError, 'differs'):
            prepare(self.work, source_workspace=self.seed)
        self.assertFalse((self.work / '_build').exists())

    def test_tracked_and_staged_changes_are_rejected(self):
        (self.source / 'source.txt').write_text('changed\n')
        for staged in (False, True):
            if staged:
                self.run_git('add', 'source.txt')
            with self.assertRaisesRegex(ValueError, 'tracked changes'):
                prepare(self.work, source_workspace=self.seed)

    def test_existing_incorrect_path_is_preserved(self):
        target = self.work / self.record['path']
        target.parent.mkdir(parents=True)
        target.write_text('preserve this file\n')
        with self.assertRaisesRegex(ValueError, 'missing'):
            prepare(self.work, source_workspace=self.seed)
        self.assertEqual(target.read_text(), 'preserve this file\n')

    def test_gate_refuses_before_Dune_when_seed_is_missing(self):
        root = Path(__file__).resolve().parents[1]
        (self.work / 'tools').mkdir()
        (self.work / 'tools/gate_workspace.py').write_bytes(
            (root / 'tools/gate_workspace.py').read_bytes())
        (self.work / 'Makefile').write_bytes((root / 'Makefile').read_bytes())
        result = subprocess.run(['make', 'check-signatures', 'GUARD=/missing',
            'PYTHON=python3', 'GATE_SOURCE_WORKSPACE=' + str(self.seed / 'missing')],
            cwd=self.work, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        self.assertNotEqual(result.returncode, 0)
        self.assertIn('Gate workspace preparation failed', result.stdout)
        self.assertNotIn('dune build', result.stdout)


if __name__ == '__main__':
    unittest.main()
