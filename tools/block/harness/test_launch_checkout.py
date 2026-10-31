"""Test immutable launch identity without a prover or an admission request."""
import hashlib
import json
from pathlib import Path
import subprocess
import tempfile
import unittest

import scratch
import harness_commit


class LaunchCheckoutTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.script = self.root / 'tools/block/harness/scratch.py'
        self.script.parent.mkdir(parents=True)
        self.script.write_text("print('launch fixture')\n")
        (self.root / '.gitignore').write_text('.worktrees/\n')
        self.git('init', '-q')
        self.git('add', '.')
        self.commit('launch')
        self.launch = self.git('rev-parse', 'HEAD')

    def git(self, *args, root=None):
        return subprocess.check_output(['git', '-C', str(root or self.root), *args], text=True).strip()

    def commit(self, message):
        self.git('-c', 'user.name=Test', '-c', 'user.email=test@example.invalid',
                 '-c', 'commit.gpgsign=false', '-c', 'core.hooksPath=/dev/null', 'commit', '-qm', message)

    def advance(self):
        self.script.write_text("print('later fixture')\n")
        self.git('add', '.')
        self.commit('later')
        return self.git('rev-parse', 'HEAD')

    def test_launch_remains_valid_after_source_head_advances(self):
        value = harness_commit.pin(self.launch, self.root)
        other = self.advance()
        self.assertNotEqual(other, self.launch)
        self.assertNotEqual(Path(value['root']), self.root)
        self.assertEqual(harness_commit.check(value), value)
        self.assertEqual(self.git('rev-parse', 'HEAD', root=Path(value['root'])), self.launch)
        self.assertEqual((Path(value['root']) / 'tools/block/harness/scratch.py').read_text(),
                         "print('launch fixture')\n")

    def test_prepare_bootstrap_reexecutes_the_pinned_checkout(self):
        recorded = []
        class Replaced(Exception):
            pass
        def execute(command, argv):
            recorded.append((command, argv))
            raise Replaced()
        with self.assertRaises(Replaced):
            harness_commit.bootstrap(self.script, ['--harness-commit', self.launch], execute=execute)
        target = Path(recorded[0][1][2])
        self.assertEqual(target.parents[3], harness_commit.destination(self.root, self.launch))
        self.assertEqual(recorded[0][1][3:], ['--harness-commit', self.launch])

    def test_bound_run_uses_launch_pin_after_source_head_advances(self):
        value = harness_commit.pin(self.launch, self.root)
        runtime = self.root / 'RUNTIME.json'
        runtime.write_text(json.dumps({'harness': value}))
        fingerprint = hashlib.sha256(runtime.read_bytes()).hexdigest()
        self.advance()
        class Replaced(Exception):
            pass
        def execute(command, argv):
            self.assertEqual(Path(argv[2]).parents[3], Path(value['root']))
            self.assertEqual(argv[3:], ['--run', str(runtime), fingerprint])
            raise Replaced()
        with self.assertRaises(Replaced):
            harness_commit.bootstrap(self.script, ['--run', str(runtime), fingerprint], execute=execute)

    def test_changed_runtime_binding_refuses_before_dispatch(self):
        runtime = self.root / 'RUNTIME.json'
        runtime.write_text(json.dumps({'harness': {'commit': self.launch}}))
        with self.assertRaisesRegex(ValueError, 'runtime binding changed'):
            harness_commit.bootstrap(self.script, ['--run', str(runtime), '0' * 64])

    def test_changed_managed_checkout_refuses(self):
        value = harness_commit.pin(self.launch, self.root)
        (Path(value['root']) / 'tools/block/harness/scratch.py').write_text('changed\n')
        with self.assertRaisesRegex(ValueError, 'uncommitted changes'):
            harness_commit.check(value)

    def test_wrong_managed_head_refuses(self):
        value = harness_commit.pin(self.launch, self.root)
        other = self.advance()
        self.git('checkout', '-q', '--detach', other, root=Path(value['root']))
        with self.assertRaisesRegex(ValueError, 'another commit'):
            harness_commit.check(value)

    def test_wrong_source_pin_still_refuses(self):
        self.advance()
        with self.assertRaisesRegex(ValueError, 'another commit'):
            harness_commit.pin(self.launch, self.root)

    def test_dirty_source_still_refuses(self):
        self.script.write_text('uncommitted\n')
        with self.assertRaisesRegex(ValueError, 'uncommitted changes'):
            harness_commit.pin(self.launch, self.root)

    def test_existing_foreign_directory_refuses(self):
        target = harness_commit.destination(self.root, self.launch)
        target.mkdir(parents=True)
        with self.assertRaisesRegex(ValueError, 'checkout root'):
            harness_commit.pin(self.launch, self.root)

    def test_checkout_symlink_refuses(self):
        target = harness_commit.destination(self.root, self.launch)
        target.parent.mkdir(parents=True)
        target.symlink_to(self.root, target_is_directory=True)
        with self.assertRaisesRegex(ValueError, 'symlink'):
            harness_commit.pin(self.launch, self.root)

    def test_repeated_pin_reuses_one_detached_checkout(self):
        first = harness_commit.pin(self.launch, self.root)
        second = harness_commit.pin(self.launch, self.root)
        self.assertEqual(first, second)
        self.assertEqual(self.git('worktree', 'list', '--porcelain').count('worktree '), 2)

    def test_old_mutable_record_is_not_relabelled(self):
        old = {'schema': 'block.shared-harness.git.v1', 'root': str(self.root),
               'commit': self.launch, 'tree': self.git('rev-parse', self.launch + ':tools/block/harness')}
        harness_commit.check(old)
        self.advance()
        with self.assertRaisesRegex(ValueError, 'another commit'):
            harness_commit.check(old)


if __name__ == '__main__':
    unittest.main()
