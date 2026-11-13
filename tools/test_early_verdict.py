"""Check the early-verdict budgets, the stage-marker caller copy and the block monitor."""

from pathlib import Path
import contextlib
import io
import json
import os
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parent))
import early_verdict as E

CALLER = '''Require Import ZesuSsz.Automation2.All.
Local Open Scope Z_scope.

Definition DesignedEntry_1 := True.

Lemma DesignedBoundary_1 : True.
Proof.
  zesu_block2.
Qed.
'''


def pass_line(user):
    return 'Tactic call zesu_run ran for %.3f secs (%.3fu,0.s) (success)\n' % (user, user)


class Fixture(unittest.TestCase):
    def setUp(self):
        temp = tempfile.TemporaryDirectory()
        self.addCleanup(temp.cleanup)
        self.root = Path(temp.name)

    def run_dir(self, sweep, name, returncode, cpu, rss_gib, log, progress=None):
        directory = sweep / 'runs' / name
        directory.mkdir(parents=True)
        (directory / 'run.log').write_text(log)
        if returncode is not None:
            (directory / 'measure.json').write_text(json.dumps(
                {'returncode': returncode, 'cpu_user': cpu, 'cpu_sys': 0.0, 'max_rss_kib': int(rss_gib * 2 ** 20), 'wall': cpu}))
        if progress is not None:
            (directory / 'progress.json').write_text(json.dumps(progress))
        return directory


class StageMarkerTest(Fixture):
    def test_inserted_before_first_declaration(self):
        text = E.with_stage_markers(CALLER)
        self.assertLess(text.index('Require Import ZesuSsz.Automation2.All.'), text.index(E.STAGE_MARKER_LINE))
        self.assertLess(text.index(E.STAGE_MARKER_LINE), text.index('Definition DesignedEntry_1'))
        self.assertIn('Proof.\n  zesu_block2.\nQed.', text)

    def test_idempotent(self):
        once = E.with_stage_markers(CALLER)
        self.assertEqual(E.with_stage_markers(once), once)

    def test_refuses_caller_without_automation_import(self):
        with self.assertRaises(ValueError):
            E.with_stage_markers('Lemma x : True.\nProof.\n  zesu_block2.\nQed.\n')


class CalibrateTest(Fixture):
    def sweep(self):
        sweep = self.root / 'sweep'
        sweep.mkdir()
        (sweep / 'CALLERS-W0.json').write_text(json.dumps([{'case': 'aa00', 'function': 'f'}, {'case': 'aa01', 'function': 'f'},
                                                           {'case': 'bb00', 'function': 'g'}]))
        self.run_dir(sweep, 'aa00', 0, 100.0, 1.5, pass_line(40.0) + pass_line(1.0))
        self.run_dir(sweep, 'aa00-2', 0, 90.0, 1.4, pass_line(30.0))             # the same block again
        self.run_dir(sweep, 'aa01', 0, 160.0, 2.5, pass_line(60.0))
        self.run_dir(sweep, 'bb00', 0, 50.0, 1.0, '', progress={
            'run_cpu': 20.0, 'stage_max': {'package_deferring': 12.0}})
        self.run_dir(sweep, 'bb00-2', 1, 900.0, 3.0, pass_line(800.0))           # open: not a closer
        self.run_dir(sweep, 'bb00-3', 0, 990.0, 9.0, 'resource guard: memory fence kill: x\n')
        self.run_dir(sweep, 'bb00-4', None, 0.0, 0.0, pass_line(5.0))            # killed: no measure
        return sweep

    def test_maxima_by_function(self):
        budgets = E.calibrate([(self.sweep(), None)], k=3, rss_gib=12, min_blocks=2, min_stage_blocks=1)
        f, g, overall = budgets['functions']['f'], budgets['functions']['g'], budgets['global']
        self.assertEqual((f['closers'], f['blocks'], f['cpu'], f['rss_gib']), (3, ['aa00', 'aa01'], 160.0, 2.5))
        self.assertEqual(f['run'], 60.0 + E.LOAD_ALLOWANCE)
        self.assertEqual(f['post'], 100.0)                 # 160 - 60 (first pass of aa01)
        self.assertEqual((g['closers'], g['run'], g['post']), (1, 20.0, 30.0))
        self.assertEqual(g['stages'], {'package_deferring': {'max': 12.0, 'blocks': ['bb00']}})
        self.assertEqual((overall['closers'], overall['blocks']), (4, ['f:aa00', 'f:aa01', 'g:bb00']))

    def test_memory_limit_must_exceed_closers(self):
        with self.assertRaises(ValueError):
            E.calibrate([(self.sweep(), None)], rss_gib=2.0)

    def test_function_needs_name(self):
        sweep = self.root / 'bare'
        self.run_dir(sweep, 'cc00', 0, 10.0, 1.0, '')
        with self.assertRaises(ValueError):
            E.calibrate([(sweep, None)])
        self.assertEqual(E.calibrate([(sweep, 'h')])['functions']['h']['closers'], 1)

    def test_budget_scope(self):
        budgets = E.calibrate([(self.sweep(), None)], k=3, rss_gib=12, min_blocks=2, min_stage_blocks=1)
        own = E.budget(budgets, 'f')
        self.assertEqual((own['scope'], own['total'], own['post_run']), ('function', 480.0, 300.0))
        few = E.budget(budgets, 'g')                       # one closing block: global maxima
        self.assertEqual((few['scope'], few['total']), ('global', 480.0))
        self.assertEqual(few['stages'], {'package_deferring': 36.0})
        self.assertEqual(E.budget(budgets, 'unseen')['scope'], 'global')
        budgets['min_stage_blocks'] = 2
        self.assertEqual(E.budget(budgets, 'g')['stages'], {})
        budgets['min_blocks'] = 3                          # three runs of f, but two distinct blocks
        self.assertEqual(E.budget(budgets, 'f')['scope'], 'global')

    def test_cli_writes_budgets(self):
        output = self.root / 'BUDGETS.json'
        with contextlib.redirect_stdout(io.StringIO()) as out:
            self.assertEqual(E.main(['calibrate', '--output', str(output), '--min-blocks', '1', '--min-stage-blocks', '1',
                                     str(self.sweep())]), 0)
        self.assertEqual(json.loads(out.getvalue()), {'f': [3, 2], 'g': [1, 1]})
        written = json.loads(output.read_text())
        self.assertEqual(E.budget(written, 'g')['stages'], {'package_deferring': 36.0})


LIMITS = {'function': 'f', 'scope': 'function', 'k': 3, 'total': 1000.0, 'zesu_run': 300.0, 'post_run': 200.0,
          'stages': {'package_deferring': 50.0}, 'rss_bytes': 12 * E.GIB}


class MonitorTest(Fixture):
    def monitor(self, limits=LIMITS):
        self.log = self.root / 'run.log'
        self.log.write_text('')
        self.samples = []
        return E.Monitor(limits, self.log, os.getpid(), sample=lambda: self.samples[-1] if self.samples else None)

    def step(self, monitor, cpu, gib=1.0, text=''):
        with self.log.open('a') as handle:
            handle.write(text)
        self.samples.append((cpu, gib * E.GIB))
        return monitor.poll()

    def test_no_sample_no_verdict(self):
        monitor = self.monitor()
        self.assertIsNone(monitor.poll())

    def test_first_pass_budget(self):
        monitor = self.monitor()
        self.assertIsNone(self.step(monitor, 250.0, text='A3L_REGCOL_VM_CLOSED\n'))
        verdict = self.step(monitor, 301.0)
        self.assertEqual((verdict['rule'], verdict['stage'], verdict['limit']), ('zesu_run', 'zesu_run', 300.0))

    def test_post_run_budget_counts_from_first_pass(self):
        monitor = self.monitor()
        self.assertIsNone(self.step(monitor, 280.0, text=pass_line(270.0)))
        self.assertIsNone(self.step(monitor, 470.0, text=pass_line(1.0)))
        verdict = self.step(monitor, 481.0)
        self.assertEqual((verdict['rule'], verdict['stage'], verdict['value']), ('post_run', 'post_run', 201.0))

    def test_stage_budget_names_stage(self):
        monitor = self.monitor()
        self.step(monitor, 10.0, text=pass_line(9.0))
        self.assertIsNone(self.step(monitor, 20.0, text='@@S stage "residual_cascade"\n@@S stage "package_deferring"\n'))
        self.assertIsNone(self.step(monitor, 69.0))
        verdict = self.step(monitor, 71.0)
        self.assertEqual((verdict['rule'], verdict['stage'], verdict['value']), ('stage', 'package_deferring', 51.0))
        self.assertEqual(self.step(monitor, 500.0), verdict)  # the first verdict stays

    def test_uncalibrated_stage_uses_post_run(self):
        monitor = self.monitor()
        self.step(monitor, 10.0, text=pass_line(9.0) + '@@S stage "final_pure"\n')
        verdict = self.step(monitor, 211.0)
        self.assertEqual((verdict['rule'], verdict['stage']), ('post_run', 'final_pure'))

    def test_memory_first(self):
        monitor = self.monitor()
        verdict = self.step(monitor, 5.0, gib=12.5)
        self.assertEqual((verdict['rule'], verdict['value'], verdict['limit'], verdict['stage']), ('memory', 12.5, 12.0, 'zesu_run'))

    def test_partial_line_waits_for_newline(self):
        monitor = self.monitor()
        self.step(monitor, 10.0, text='Tactic call zesu_run ran for 9.0 secs (9.0u,')
        self.assertIsNone(monitor.run_cpu)
        self.step(monitor, 11.0, text='0.s) (success)\n')
        self.assertEqual(monitor.run_cpu, 11.0)

    def test_summary_records_stages(self):
        monitor = self.monitor()
        self.step(monitor, 10.0, text=pass_line(9.0))
        self.step(monitor, 20.0, text='@@S stage "package_deferring"\n')
        self.step(monitor, 40.0, text='@@S stage "package_deferring"\n')
        self.step(monitor, 45.0)
        summary = monitor.summary()
        self.assertEqual(summary['run_cpu'], 10.0)
        self.assertEqual(summary['stage_cpu'], {'package_deferring': 25.0})
        self.assertEqual(summary['stage_max'], {'package_deferring': 20.0})
        self.assertEqual([name for _, name in summary['events']], ['zesu_run', 'package_deferring', 'package_deferring'])

    def test_closer_record_reads_summary(self):
        monitor = self.monitor()
        self.step(monitor, 10.0, text=pass_line(9.0))
        self.step(monitor, 30.0, text='@@S stage "package_deferring"\n')
        self.step(monitor, 45.0)
        directory = self.run_dir(self.root / 's', 'aa00', 0, 46.0, 1.0, self.log.read_text(), progress=monitor.summary())
        record = E.closer_record(directory)
        self.assertEqual((record['run'], record['post'], record['stages']), (10.0, 36.0, {'package_deferring': 15.0}))


class ScopeTest(unittest.TestCase):
    def test_process_outside_guard_scope(self):
        self.assertIsNone(E.scope_cgroup(os.getpid()))
        self.assertIn(os.getpid(), E.descendants(os.getpid()))

    def test_missing_cgroup_reads_none(self):
        self.assertIsNone(E.read_cgroup(Path('/nonexistent-cgroup')))

    def test_block_scope_name(self):
        self.assertTrue(E.BLOCK_SCOPE.search('/s/zesudet-heldout-w0c3-39a4-1603530-28459.scope'))
        self.assertFalse(E.BLOCK_SCOPE.search('/s/zesudet-batch-heldout-w0-c3-1-1594941.scope'))
        self.assertFalse(E.BLOCK_SCOPE.search('/s/tmux-spawn-1.scope'))


if __name__ == '__main__':
    unittest.main()
