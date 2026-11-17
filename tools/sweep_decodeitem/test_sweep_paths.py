"""Path resolution of the decodeItem sweep: everything comes from the checkout holding the scripts."""
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import mksweep
import sweep_paths

SCRIPTS = sorted(p for p in HERE.iterdir() if p.suffix in ('.sh', '.py') and not p.name.startswith('test_'))


def git(*args, cwd):
    subprocess.run(['git', *args], cwd=cwd, check=True, capture_output=True)


class NoBakedPaths(unittest.TestCase):
    def test_no_worktree_or_agent_paths(self):
        for p in SCRIPTS:
            text = p.read_text()
            for bad in ('.worktrees/', 'integration-1', '/home/cody/zesislar', 'worker-build-'):
                self.assertNotIn(bad, text, '%s mentions %s' % (p.name, bad))


class Resolution(unittest.TestCase):
    def test_repo_and_guard_follow_this_checkout(self):
        repo = sweep_paths.repo_root()
        self.assertEqual(repo, HERE.parents[1])
        self.assertTrue((repo / '.git').exists())
        self.assertEqual(sweep_paths.guard(), repo / 'tools' / 'resource_guard.sh')
        self.assertTrue(sweep_paths.guard().exists())

    def test_copied_checkout_resolves_to_the_copy(self):
        with tempfile.TemporaryDirectory() as t:
            main, wt = Path(t, 'main'), Path(t, 'main', '.worktrees', 'other')
            main.mkdir()
            git('init', '-q', cwd=main)
            git('-c', 'user.name=t', '-c', 'user.email=t@t', 'commit', '-q', '--allow-empty', '-m', 'x', cwd=main)
            git('worktree', 'add', '-q', '--detach', str(wt), cwd=main)
            tool = wt / 'tools' / 'sweep_decodeitem'
            tool.mkdir(parents=True)
            shutil.copy(HERE / 'sweep_paths.py', tool)
            env = {k: v for k, v in os.environ.items() if k != 'SWEEP_ROOT'}
            run = lambda what: subprocess.run([sys.executable, str(tool / 'sweep_paths.py'), what], env=env,
                                              capture_output=True, text=True, check=True).stdout.strip()
            self.assertEqual(run('repo'), str(wt.resolve()))
            self.assertEqual(run('guard'), str(wt.resolve() / 'tools' / 'resource_guard.sh'))
            # results are shared: they live under the primary checkout, not the worktree
            self.assertEqual(run('out'), str(main.resolve() / '_build' / 'agents' / 'mergeq'))
            env['SWEEP_ROOT'] = t
            self.assertEqual(run('out'), str(Path(t).resolve()))


class Plan(unittest.TestCase):
    def test_offset_callers_and_out_root(self):
        with tempfile.TemporaryDirectory() as t:
            t = Path(t); (t / 'bank').mkdir(); (t / 'callers').mkdir()
            (t / 'bank' / 'ARGS.json').write_text('["coqc"]')
            (t / 'callers' / 'Caller0014.v').write_text('')
            old = dict(os.environ)
            os.environ['SWEEP_ROOT'] = str(t / 'out'); os.environ.pop('CALLER_BASE', None)
            try:
                mksweep.main(['mksweep.py', 'x', str(t / 'bank'), str(t / 'callers'), '6974'])
            finally:
                os.environ.clear(); os.environ.update(old)
            jobs = json.loads((t / 'out' / 'sweep' / 'x' / 'jobs-6974.json').read_text())
            self.assertEqual(jobs[0]['cmd'], ['coqc', 'Caller0014.v'])
            self.assertTrue((t / 'out' / 'sweep' / 'x' / '6974' / 'Caller0014.v').exists())


if __name__ == '__main__':
    unittest.main()
