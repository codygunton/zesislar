"""Closure certificates: only the unmodified generated caller, compiled at Qed with coqc exit 0 and
closed assumptions on an unmodified bank, is closed; a wrapper's exit status never is."""
from contextlib import redirect_stdout
import io
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest
import unittest.mock

sys.path.insert(0, str(Path(__file__).resolve().parent))
import closure_cert as C
import sweep
import sweep_outcome as S

TOOLS = Path(__file__).resolve().parent
COQC = shutil.which('coqc') or str(Path.home() / 'islaris' / '_opam' / 'bin' / 'coqc')
CALLERS = 'tools/block/generated/x_callers'
CLOSED = b'Lemma DesignedBoundary_1 : True.\nProof.\n  exact I.\nQed.\n\nPrint Assumptions DesignedBoundary_1.\n'
INCOMPLETE = b'Lemma DesignedBoundary_2 : True.\nProof.\n  idtac.\nQed.\n\nPrint Assumptions DesignedBoundary_2.\n'
# Exit 0 whatever the command does, like the resource guard's batch and scope did on 2026-11-16.
GUARD = '#!/bin/sh\nwhile [ "$1" != "--" ]; do shift; done\nshift\n"$@"\nexit 0\n'


def git(workspace, *args):
    return subprocess.run(['git', '-C', str(workspace), *args], check=True, capture_output=True,
                          text=True).stdout.strip()


@unittest.skipUnless(Path(COQC).is_file(), 'coqc is not installed')
class ClosureCertificate(unittest.TestCase):
    def setUp(self):
        self.root = Path(tempfile.mkdtemp())
        self.addCleanup(shutil.rmtree, self.root)
        self.workspace = self.root / 'ws'
        (self.workspace / CALLERS).mkdir(parents=True)
        (self.workspace / CALLERS / 'Caller0001.v').write_bytes(CLOSED)
        (self.workspace / CALLERS / 'Caller0002.v').write_bytes(INCOMPLETE)
        (self.workspace / 'ZesuSsz').mkdir()
        (self.workspace / 'ZesuSsz' / 'Rules.v').write_text('Ltac production_rule := exact I.\n')
        (self.workspace / '.gitignore').write_text('_build/\n')
        git(self.workspace, 'init', '-q')
        git(self.workspace, 'add', '.')
        git(self.workspace, '-c', 'user.name=t', '-c', 'user.email=t@t', 'commit', '-qm', 'callers')
        self.head = git(self.workspace, 'rev-parse', 'HEAD')
        self.bank = self.workspace / '_build' / 'bank'
        (self.bank / 'default' / 'ZesuSsz').mkdir(parents=True)
        shutil.copyfile(self.workspace / 'ZesuSsz' / 'Rules.v', self.bank / 'default' / 'ZesuSsz' / 'Rules.v')
        self.run_dir = self.root / 'run'
        self.run_dir.mkdir()

    def caller(self, case, data=None):
        path = self.run_dir / ('Caller%s.v' % case)
        path.write_bytes(data if data is not None else (self.workspace / CALLERS / path.name).read_bytes())
        return path

    def measured(self, caller, *flags, time=True):
        """Compile with tools/measure.py in the run directory; return the measure record path."""
        command = [COQC] + (['-time'] if time else []) + ['-Q', str(self.bank / 'default' / 'ZesuSsz'), 'ZesuSsz',
                                                         *flags, '-o', caller.with_suffix('.vo').name, caller.name]
        subprocess.run([sys.executable, str(TOOLS / 'measure.py'), 'measure.json', '--', *command],
                       cwd=self.run_dir, capture_output=True)
        return self.run_dir / 'measure.json'

    def verdict(self, case, caller, measure):
        return C.verdict(case, caller, self.bank, measure, out=self.run_dir)

    def test_unmodified_closed_caller_is_certified(self):
        caller = self.caller('0001')
        record = self.verdict('0001', caller, self.measured(caller))
        self.assertEqual(record['verdict'], 'CLOSED', record.get('reason'))
        self.assertEqual(record['head'], self.head)
        self.assertEqual(record['generated_caller'], CALLERS + '/Caller0001.v')
        self.assertEqual(record['coqc_returncode'], 0)
        for key in ('caller_sha256', 'log_sha256', 'bank_sources_sha256', 'cpu_seconds', 'max_rss_kib', 'vo'):
            self.assertIn(key, record)
        self.assertTrue((self.run_dir / 'CLOSURE.json').is_file())
        self.assertFalse((self.run_dir / 'NOT-CLOSED.json').exists())
        self.assertEqual(C.done_line(record), 'RUN-DONE case=0001 coqc_rc=0 verdict=CLOSED')

    def test_incomplete_proof_with_wrapper_exit_zero_is_not_closed(self):
        guard = self.root / 'guard.sh'
        guard.write_text(GUARD)
        guard.chmod(0o755)
        (self.bank / 'coqc_recipe.json').write_text(json.dumps(
            {'command': ['coqc', '-q', '-Q', 'ZesuSsz', 'ZesuSsz', 'ZesuSsz/Rules.v'],
             'working_dir': str(self.bank / 'default')}))
        caller = self.caller('0002')
        os.environ['ZESU_RESOURCE_GUARD'] = str(guard)
        self.addCleanup(os.environ.pop, 'ZESU_RESOURCE_GUARD')
        wrapper_exit = C.compile_caller('0002', caller, self.bank, self.run_dir, coqc=COQC)
        self.assertEqual(wrapper_exit, 0)
        record = C.verdict('0002', caller, self.bank, self.run_dir / 'measure.json', out=self.run_dir)
        self.assertEqual(record['verdict'], 'NOT-CLOSED')
        self.assertEqual(record['reason'], 'coqc exit 1')
        self.assertTrue((self.run_dir / 'NOT-CLOSED.json').is_file())
        self.assertFalse((self.run_dir / 'CLOSURE.json').exists())
        self.assertEqual(C.done_line(record), 'RUN-DONE case=0002 coqc_rc=1 verdict=NOT-CLOSED reason="coqc exit 1"')
        # The shared sweep prints coqc's status and the verdict, never the wrapper's 0.
        # sweep finds coqc on PATH; a tools/bg scope has no opam PATH, so put COQC's dir first.
        output = io.StringIO()
        path = os.path.dirname(COQC) + os.pathsep + os.environ.get('PATH', '')
        with redirect_stdout(output), unittest.mock.patch.dict(os.environ, {'PATH': path}):
            sweep.main(['--build', str(self.bank), '--callers', 'x_callers', '--run-dir', str(self.root / 'sweep'),
                        '0002', '0001'])
        lines = output.getvalue().splitlines()
        self.assertIn('RUN-DONE case=0002 coqc_rc=1 verdict=NOT-CLOSED reason="coqc exit 1"', lines)
        self.assertIn('RUN-DONE case=0001 coqc_rc=0 verdict=CLOSED', lines)
        rows = {row['case']: row for row in
                map(json.loads, (self.root / 'sweep' / 'sweep.jsonl').read_text().splitlines())}
        self.assertEqual((rows['0002']['closed'], rows['0002']['returncode'], rows['0002']['wrapper_exit']),
                         (False, 1, 0))
        self.assertEqual(S.row_outcome(rows['0002']), 'open')
        self.assertEqual(S.row_outcome(rows['0001']), 'closed')

    def test_modified_caller_is_not_closed(self):
        caller = self.caller('0001', b'(* scaffold *)\n' + CLOSED)
        measure = self.measured(caller)
        self.assertEqual(json.loads(measure.read_text())['returncode'], 0)
        record = self.verdict('0001', caller, measure)
        self.assertEqual(record['verdict'], 'NOT-CLOSED')
        self.assertIn('differs from the generated ' + CALLERS + '/Caller0001.v', record['reason'])

    def test_caller_changed_after_the_compile_is_not_closed(self):
        caller = self.caller('0001')
        measure = self.measured(caller)
        caller.write_bytes(CLOSED + b'\n')
        self.assertEqual(self.verdict('0001', caller, measure)['verdict'], 'NOT-CLOSED')

    def test_log_without_the_qed_record_is_not_closed(self):
        caller = self.caller('0001')
        record = self.verdict('0001', caller, self.measured(caller, time=False))
        self.assertEqual(record['verdict'], 'NOT-CLOSED')
        self.assertIn('no -time record of the Qed of DesignedBoundary_1', record['reason'])

    def test_rules_loaded_from_outside_the_bank_are_not_closed(self):
        scratch = self.root / 'scratch'
        scratch.mkdir()
        (scratch / 'Override.v').write_text('Ltac scratch_rule := fail.\nLtac scratch_rule ::= exact I.\n')
        caller = self.caller('0001')
        record = self.verdict('0001', caller, self.measured(caller, '-Q', str(scratch), 'ZesuSsz.Scratch'))
        self.assertEqual(record['verdict'], 'NOT-CLOSED')
        self.assertIn('is outside the bank', record['reason'])
        record = self.verdict('0001', caller, self.measured(caller, '-l', str(scratch / 'Override.v')))
        self.assertEqual(record['verdict'], 'NOT-CLOSED')
        self.assertIn('option -l is not allowed', record['reason'])

    def test_bank_rules_that_differ_from_head_are_not_closed(self):
        (self.bank / 'default' / 'ZesuSsz' / 'Rules.v').write_text(
            'Ltac production_rule := exact I.\nLtac production_rule ::= idtac.\n')
        caller = self.caller('0001')
        record = self.verdict('0001', caller, self.measured(caller))
        self.assertEqual(record['verdict'], 'NOT-CLOSED')
        self.assertIn('differs from ZesuSsz/Rules.v at', record['reason'])

    def test_untracked_bank_redefinition_is_not_closed(self):
        (self.bank / 'default' / 'ZesuSsz' / 'Scaffold.v').write_text('Ltac production_rule ::= idtac.\n')
        caller = self.caller('0001')
        record = self.verdict('0001', caller, self.measured(caller))
        self.assertEqual(record['verdict'], 'NOT-CLOSED')
        self.assertIn('redefines a tactic', record['reason'])


class LogCheck(unittest.TestCase):
    def test_assumptions_must_be_closed(self):
        log = ('Chars 46 - 50 [Qed.] 0. secs (0.u,0.s)\nAxioms:\nbar : 1 = 1\n'
               'Chars 52 - 74 [Print~Assumptions~foo.] 0. secs (0.u,0.s)\n')
        with self.assertRaises(C.NotClosed):
            C.check_log(log, 'foo', (46, 50), (52, 74))
        C.check_log(log.replace('Axioms:\nbar : 1 = 1', C.CLOSED_TEXT), 'foo', (46, 50), (52, 74))


if __name__ == '__main__':
    unittest.main()
