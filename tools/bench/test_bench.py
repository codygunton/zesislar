"""Check that bench.py gives a bank a coqc recipe before any block runs (tools/bench/bench.py)."""

import contextlib
import io
import json
import os
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest
from unittest import mock

import bench

FAKE_OPAM = '''#!/usr/bin/env python3
import os, shutil, sys
arguments = sys.argv[1:]
with open(os.environ['FAKE_RULES_ARGS'], 'a') as out:
    out.write(' '.join(arguments) + '\\n')
shutil.copy(os.environ['FAKE_RULES'], arguments[arguments.index('-o') + 1])
'''
HEAD = 'c' * 40
TARGETS = ['ZesuSsz/Automation2/All.vo', 'ZesuSsz/Generated/X/Entries.vo']


class CacheOnlyBank(unittest.TestCase):
    """A bank whose Dune build came wholly from the cache: BANK.json says rc 0, the trace ran no coqc."""

    def setUp(self):
        temporary = tempfile.TemporaryDirectory(prefix='bench-recipe-')
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name).resolve()
        self.workspace = self.root / 'workspace'
        (self.workspace / '_build').mkdir(parents=True)
        (self.workspace / 'tools').symlink_to(bench.TOOLS, target_is_directory=True)
        self.bank = self.workspace / '_build' / 'agents' / 'bench-k1'
        self.bank.mkdir(parents=True)
        (self.bank / 'BANK.json').write_text(json.dumps({'head': HEAD, 'targets': TARGETS, 'prep_rc': 0, 'rc': 0,
                                                         'missing': []}))
        (self.bank / 'trace.csexp').write_bytes(b'')
        (self.bank / 'install' / 'default' / 'lib').mkdir(parents=True)
        fake = self.root / 'fakebin'
        fake.mkdir()
        (fake / 'opam').write_text(FAKE_OPAM)
        (fake / 'opam').chmod(0o755)
        self.rules = self.root / 'rules.json'
        self.calls = self.root / 'calls.txt'
        self.calls.write_text('')
        environment = {'PATH': str(fake) + os.pathsep + os.environ.get('PATH', ''),
                       'FAKE_RULES': str(self.rules), 'FAKE_RULES_ARGS': str(self.calls),
                       'TMPDIR': str(self.root)}
        patches = [mock.patch.dict(os.environ, environment), mock.patch.object(bench, 'ISLARIS', self.root / 'islaris')]
        for patch in patches:
            patch.start()
            self.addCleanup(patch.stop)
        self.logged = []

    def write_rules(self, program, source):
        logical = str(self.workspace / '_dune-cache' / 'default')
        self.rules.write_text(json.dumps([{'deps': [], 'targets': [], 'context': 'default', 'action': [
            'chdir', logical, ['run', program, '-q', '-R', '.', 'ZesuSsz', '-o', 'out.vo', source]]}]))

    def build(self):
        return bench.build_bank(self.workspace, 'k1', HEAD, TARGETS, {}, self.logged.append)

    def test_recipe_comes_from_dune_rules(self):
        self.write_rules('.bin/coqc', 'ZesuSsz/Automation2/All.v')
        self.assertEqual(self.build(), self.bank)
        recipe = json.loads((self.bank / 'coqc_recipe.json').read_text())
        self.assertEqual(recipe['command'][0], '.bin/coqc')
        self.assertIn('ZesuSsz/Automation2/All.v', recipe['command'])
        # The rules ran under the canonical alias; the saved recipe names the physical bank.
        self.assertEqual(recipe['working_dir'], str(self.bank / 'default'))
        calls = self.calls.read_text().splitlines()
        self.assertEqual(len(calls), 1)
        self.assertIn('dune rules --format=json', calls[0])
        self.assertTrue(calls[0].endswith(' ' + TARGETS[0]))
        # The block compile reads it back.
        command, working = bench.C.recipe_command(self.bank, Path('/usr/bin/coqc'), self.root / 'Caller.v',
                                                  self.root / 'Caller.vo')
        self.assertEqual(command[:3], ['/usr/bin/coqc', '-time', '-q'])
        self.assertEqual(working, self.bank / 'default')

    def test_existing_recipe_is_kept(self):
        recipe = {'command': ['.bin/coqc', '-q', 'ZesuSsz/A.v'], 'working_dir': str(self.bank / 'default')}
        (self.bank / 'coqc_recipe.json').write_text(json.dumps(recipe))
        self.build()
        self.assertEqual(self.calls.read_text(), '')
        self.assertEqual(json.loads((self.bank / 'coqc_recipe.json').read_text()), recipe)

    def test_no_recipe_refuses_once_up_front(self):
        self.write_rules('/bin/cp', 'ZesuSsz/Automation2/All.v')
        stderr = io.StringIO()
        with contextlib.redirect_stderr(stderr), self.assertRaises(SystemExit) as stop:
            self.build()
        self.assertEqual(stop.exception.code, 3)
        lines = stderr.getvalue().splitlines()
        self.assertEqual(len(lines), 1)
        self.assertTrue(lines[0].startswith('refused: '))
        self.assertIn('--cache=disabled', lines[0])
        self.assertFalse((self.bank / 'coqc_recipe.json').exists())

    def test_cache_only_bank_gets_the_findlib_record(self):
        recipe = {'command': ['.bin/coqc', '-q', 'ZesuSsz/A.v'], 'working_dir': str(self.bank / 'default')}
        (self.bank / 'coqc_recipe.json').write_text(json.dumps(recipe))
        self.build()
        record = json.loads((self.bank / 'coqc-ocamlpath.json').read_text())
        self.assertEqual(record, {'schema_version': 1, 'workspace': str(self.workspace),
                                  'private_build': str(self.bank),
                                  'OCAMLPATH': str(self.bank / 'install' / 'default' / 'lib')})
        self.assertEqual(bench.check_record(record, self.workspace, self.bank), record['OCAMLPATH'])
        # A record Dune's coqc route wrote is kept as it is.
        (self.bank / 'coqc-ocamlpath.json').write_text('{"kept": 1}')
        self.build()
        self.assertEqual((self.bank / 'coqc-ocamlpath.json').read_text(), '{"kept": 1}')

    def test_no_findlib_directory_refuses(self):
        recipe = {'command': ['.bin/coqc', '-q', 'ZesuSsz/A.v'], 'working_dir': str(self.bank / 'default')}
        (self.bank / 'coqc_recipe.json').write_text(json.dumps(recipe))
        (self.bank / 'install' / 'default' / 'lib').rmdir()
        with contextlib.redirect_stderr(io.StringIO()), self.assertRaises(SystemExit) as stop:
            self.build()
        self.assertEqual(stop.exception.code, 3)
        self.assertFalse((self.bank / 'coqc-ocamlpath.json').exists())


COQC = shutil.which('coqc') or next((str(path) for path in [Path('/home/cody/islaris/_opam/bin/coqc')]
                                     if path.is_file()), None)


class DumpLeftover(unittest.TestCase):
    """--dump-leftover prints the goals a block leaves when the export skipped them (spatial goals)."""

    TINY = 'Lemma tiny : 1 = 2 /\\ True.\nProof.\n  split.\nQed.\n'

    @unittest.skipIf(COQC is None, 'no coqc')
    def test_a_tiny_failing_lemma_prints_its_goals(self):
        with tempfile.TemporaryDirectory(prefix='bench-dump-') as directory:
            source = Path(directory) / 'Tiny.v'
            source.write_text(self.TINY)
            self.assertNotEqual(subprocess.run([COQC, '-q', str(source)], capture_output=True).returncode, 0)
            source.write_text(bench.dump_caller_text(self.TINY))
            done = subprocess.run([COQC, '-q', '-time', str(source)], capture_output=True, text=True)
            self.assertEqual(done.returncode, 0, done.stdout + done.stderr)
        goals = bench.final_goals(done.stdout)
        self.assertTrue(goals.startswith('2 goals'), goals)
        self.assertIn('1 = 2', goals)
        self.assertIn('True', goals)
        self.assertNotIn('Chars ', goals)

    def test_dump_only_for_skipped_goals_and_saved_beside_the_leftovers(self):
        self.assertIsNone(bench.dump_caller_text('Lemma x : True.\nProof.\n  exact I.\nDefined.\n'))
        with tempfile.TemporaryDirectory(prefix='bench-dump-') as directory:
            directory = Path(directory)
            caller = directory / 'Caller0230.v'
            caller.write_text(self.TINY)
            member, context = {'case': '0230', 'claim_gib': 3}, {'bank': directory}
            caps = {'limit_gib': 16, 'cpu_seconds': 100}

            def compile_caller(case, source, bank, out, limit, cpu, name, claim_gib):
                self.assertEqual((source.name, source.read_text().splitlines()[-2:], limit, cpu, claim_gib),
                                 ('Caller0230.v', ['Show.', 'Abort.'], 16, 100, 3))
                (out / 'measure.json.log').write_text('@@X skip final spatial\n1 goal\n  x : Z\n  ====\n  P x\n'
                                                      'Chars 0 - 5 [Show.] 0. secs\n')
                return 0

            with mock.patch.object(bench.R, 'load_block', return_value={'leftovers': [{'status': 'pure',
                                                                                        'statement': 'P'}]}), \
                    mock.patch.object(bench.C, 'compile_caller', side_effect=compile_caller) as compiled:
                self.assertIsNone(bench.dump_leftover(member, directory, caller, context, caps, 'run'))
                self.assertFalse(compiled.called)
            with mock.patch.object(bench.R, 'load_block', return_value={'leftovers': [{'status': 'skip'}]}), \
                    mock.patch.object(bench.C, 'compile_caller', side_effect=compile_caller):
                saved = bench.dump_leftover(member, directory, caller, context, caps, 'run')
            self.assertEqual(saved, str(directory / 'leftover' / 'FINAL-GOAL.txt'))
            self.assertEqual(Path(saved).read_text(), '1 goal\n  x : Z\n  ====\n  P x\n')
            self.assertEqual(caller.read_text(), self.TINY)


class MemberCpuCap(unittest.TestCase):
    """A member's own "cpu_seconds" replaces the set's CPU cap; a member without it keeps the set's."""

    def compile_cap(self, member):
        temporary = tempfile.TemporaryDirectory(prefix='bench-cap-')
        self.addCleanup(temporary.cleanup)
        options = mock.Mock(run_dir=Path(temporary.name))
        context = {'workspace': Path(temporary.name), 'bench_head': HEAD, 'bank': Path(temporary.name),
                   'caps': {'cpu_seconds': 3600, 'limit_gib': 24}}
        with mock.patch.object(bench.subprocess, 'run', return_value=mock.Mock(stdout=b'')), \
                mock.patch.object(bench, 'Sampler'), \
                mock.patch.object(bench.C, 'compile_caller', return_value=0) as compile_caller, \
                mock.patch.object(bench.C, 'verdict', return_value={'verdict': 'CLOSED'}), \
                mock.patch.object(bench.C, 'done_line', return_value='done'), \
                mock.patch.object(bench, 'save_leftovers', return_value=None), \
                contextlib.redirect_stdout(io.StringIO()):
            bench.run_member(member, options, context)
        arguments = compile_caller.call_args.args
        return arguments[4], arguments[5]  # limit_gib, cpu

    def test_member_cap_wins(self):
        member = {'function': 'nextUint64', 'callers': 'c', 'case': '0044', 'cpu_seconds': 300}
        self.assertEqual(self.compile_cap(member), (24, 300))

    def test_set_cap_without_member_cap(self):
        member = {'function': 'nextUint64', 'callers': 'c', 'case': '0044'}
        self.assertEqual(self.compile_cap(member), (24, 3600))


if __name__ == '__main__':
    unittest.main()
