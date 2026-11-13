"""Check the build janitor's budget, plan, deletions, and admission in temporary trees."""

import argparse
import gzip
import io
import json
import os
from pathlib import Path
import subprocess
import tempfile
import time
import unittest
from unittest.mock import patch

import build_janitor as J
from reflink_copy import ReflinkError, reflink_copy

TOOLS = Path(__file__).resolve().parent
HOUR = 3600


def write(path, data=b'x'):
    path = Path(path)
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_bytes(data)
    return path


class JanitorTree(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name) / 'repo'
        self.agents = self.root / '_build/agents'
        self.proc = Path(self.temp.name) / 'proc'
        self.proc.mkdir()
        # Files cannot get an old ctime, so the janitor's clock moves forward instead.
        self.now = time.time() + 25 * HOUR

    def fresh(self, path):
        """Give PATH and everything under it a change within the last 24 h of self.now."""
        stamp = self.now - HOUR
        for directory, _, files in os.walk(path):
            for name in files:
                os.utime(os.path.join(directory, name), (stamp, stamp), follow_symlinks=False)
            os.utime(directory, (stamp, stamp))

    def janitor(self, **options):
        options.setdefault('now', self.now)
        options.setdefault('jobs', 1)
        return J.Janitor(self.root, log_dir=self.root / '_build/janitor', **options)

    def live(self, *paths):
        for index, path in enumerate(paths):
            entry = self.proc / str(1000 + index)
            entry.mkdir()
            (entry / 'cwd').symlink_to(path)
        return J.LivePaths.scan(self.root, proc=self.proc)

    def plan_and_apply(self, janitor, live):
        runs = janitor.survey_runs()
        plan = janitor.plan(runs, live)
        log = io.StringIO()
        janitor.apply(plan, live, log)
        return plan, log.getvalue()


class Measurement(JanitorTree):
    def test_union_counts_overlapping_extents_once(self):
        self.assertEqual(J.union_bytes({0: 10, 5: 10, 30: 5}), 20)
        self.assertEqual(J.union_bytes({0: 10, 2: 3}), 10)
        self.assertEqual(J.union_bytes({}), 0)

    def test_budget_marks_agents_over_their_share_and_never_orch_refusable(self):
        write(self.agents / 'a/run1/data.bin', os.urandom(3 << 20))
        write(self.agents / 'orch/run/data.bin', os.urandom(3 << 20))
        write(self.agents / 'b/run1/data.bin', os.urandom(1 << 20))
        janitor = self.janitor(agent_budget=2 << 20, total_budget=4 << 20)
        budget = janitor.budget(janitor.survey_runs())
        self.assertGreaterEqual(budget['agents']['a']['unique_bytes'], 3 << 20)
        self.assertTrue(budget['agents']['a']['over'])
        self.assertFalse(budget['agents']['b']['over'])
        self.assertTrue(budget['agents']['orch']['over'])
        self.assertTrue(budget['agents']['orch']['protected'])
        self.assertTrue(budget['total_over'])
        self.assertGreaterEqual(budget['agents']['a']['unshared_large_json_bytes'], 0)

    def test_reflinked_copies_count_once_per_agent(self):
        parent = TOOLS.parent / '_build'
        parent.mkdir(exist_ok=True)
        with tempfile.TemporaryDirectory(prefix='janitor-reflink-', dir=parent) as directory:
            root = Path(directory)
            source = write(root / '_build/agents/a/run1/RUNTIME.json', os.urandom(4 << 20))
            os.fsync(os.open(source, os.O_RDONLY))
            try:
                reflink_copy(source, write(root / '_build/agents/a/run2/RUNTIME.json'))
            except ReflinkError as error:
                self.skipTest(f'no reflink support: {error}')
            janitor = J.Janitor(root, now=self.now, jobs=1)
            budget = janitor.budget(janitor.survey_runs())
            self.assertLess(budget['agents']['a']['unique_bytes'], 5 << 20)
            self.assertLess(budget['total_unique_bytes'], 5 << 20)


class Plan(JanitorTree):
    def test_idle_run_shrinks_to_small_and_kept_files(self):
        run = self.agents / 'a/old'
        write(run / 'Module.vo', b'object')
        write(run / 'big.json', os.urandom(2 << 20))
        write(run / 'RESULT.json', b'{}')
        write(run / 'retained/big.bin', os.urandom(2 << 20))
        write(run / 'KEEP.json', json.dumps(['retained']).encode())
        plan, log = self.plan_and_apply(self.janitor(), self.live())
        self.assertFalse((run / 'Module.vo').exists())
        self.assertFalse((run / 'big.json').exists())
        self.assertTrue((run / 'RESULT.json').exists())
        self.assertTrue((run / 'retained/big.bin').exists())
        self.assertTrue((run / 'KEEP.json').exists())
        self.assertIn(str(run / 'Module.vo'), log)
        self.assertIn(str(run / 'big.json'), log)
        row = next(row for row in plan['rows'] if row['path'] == str(run))
        self.assertEqual(row['deleted_files'], 2)

    def test_protected_runs_keep_every_file(self):
        fresh = self.agents / 'a/fresh'
        write(fresh / 'Module.vo')
        write(fresh / 'MANIFEST.json',
              json.dumps({'donor': str(self.agents / 'a/named/Donor.vo')}).encode())
        linked = write(self.agents / 'a/linked/Bank.vo')
        (fresh / 'link').symlink_to(linked)
        self.fresh(fresh)
        orch = write(self.agents / 'orch/old/Module.vo')
        named = write(self.agents / 'a/named/Donor.vo')
        used = write(self.agents / 'a/used/Module.vo')
        top = write(self.agents / 'a/default/Module.vo')
        (self.root / '_build/default').symlink_to(self.agents / 'a/default')
        plan, log = self.plan_and_apply(self.janitor(), self.live(used.parent))
        for path in (fresh / 'Module.vo', orch, named, linked, used, top):
            self.assertTrue(path.exists(), path)
        self.assertEqual(log, '')
        reasons = {row['path']: row['reason'] for row in plan['rows']}
        self.assertEqual(reasons[str(fresh)], 'changed in the last 24 h')
        self.assertEqual(reasons[str(orch.parent)], 'protected agent')
        self.assertTrue(reasons[str(named.parent)].startswith('named by a manifest'))
        self.assertTrue(reasons[str(linked.parent)].startswith('symbolic link target'))
        self.assertTrue(reasons[str(used.parent)].startswith('live process uses'))
        self.assertTrue(reasons[str(top.parent)].startswith('target of _build/default'))

    def test_sealed_run_shrinks_while_fresh(self):
        run = self.agents / 'a/sealed'
        write(run / 'Module.vo')
        write(run / 'SEALED.json', b'{}')
        self.fresh(run)
        self.plan_and_apply(self.janitor(), self.live())
        self.assertFalse((run / 'Module.vo').exists())
        self.assertTrue((run / 'SEALED.json').exists())

    def test_unreadable_keep_file_keeps_the_run(self):
        run = self.agents / 'a/old'
        write(run / 'Module.vo')
        write(run / 'KEEP.json', b'not json')
        plan, _ = self.plan_and_apply(self.janitor(), self.live())
        self.assertTrue((run / 'Module.vo').exists())
        self.assertIn('unreadable KEEP.json', [row.get('reason') for row in plan['rows']])

    def test_change_during_the_run_cancels_the_deletion(self):
        run = self.agents / 'a/old'
        write(run / 'Module.vo')
        janitor = self.janitor()
        live = self.live()
        plan = janitor.plan(janitor.survey_runs(), live)
        stamp = self.now + HOUR
        os.utime(run, (stamp, stamp))
        janitor.apply(plan, live, io.StringIO())
        self.assertTrue((run / 'Module.vo').exists())

    def test_live_process_at_apply_time_cancels_the_deletion(self):
        run = self.agents / 'a/old'
        write(run / 'Module.vo')
        janitor = self.janitor()
        plan = janitor.plan(janitor.survey_runs(), self.live())
        janitor.apply(plan, self.live(run / 'Module.vo'), io.StringIO())
        self.assertTrue((run / 'Module.vo').exists())

    def test_worktree_builds_expire_after_48_hours_and_checkouts_stay(self):
        worktrees = self.root / '.worktrees'
        old = write(worktrees / 'old/_build/default/Module.vo')
        source = write(worktrees / 'old/Source.v')
        recent = write(worktrees / 'recent/_build/default/Module.vo')
        used = write(worktrees / 'used/_build/default/Module.vo')
        write(worktrees / 'used/Source.v')
        janitor = self.janitor(now=time.time() + 49 * HOUR)
        stamp = janitor.now - 47 * HOUR
        os.utime(recent, (stamp, stamp))
        self.plan_and_apply(janitor, self.live(worktrees / 'used'))
        self.assertFalse(old.parent.parent.exists())
        self.assertTrue(source.exists())
        self.assertTrue(recent.exists())
        self.assertTrue(used.exists())

    def test_worktree_build_holding_a_ledger_receipt_stays(self):
        worktrees = self.root / '.worktrees'
        receipt = write(worktrees / 'cut/_build/native-cut/REPORT.json')
        ledger = write(self.root / 'LEDGER.json', json.dumps({'released_region_claims': {
            '6ae0': {'bytes': 1, 'receipt': str(receipt), 'sha256': '0'}}}).encode())
        janitor = self.janitor(now=time.time() + 49 * HOUR)
        with patch.dict(os.environ, {'ZESU_CANONICAL_LEDGER': str(ledger)}):
            plan, _ = self.plan_and_apply(janitor, self.live())
        self.assertTrue(receipt.exists())
        [row] = [row for row in plan['rows'] if row['kind'] == 'worktree-build']
        self.assertEqual(row['reason'], 'admission ledger receipt ' + str(receipt))

    def test_banks_of_older_main_commits_go_and_the_newest_stays(self):
        heads = self.repository(2)
        older = self.agents / 'a/bank-old'
        write(older / 'READY.json', json.dumps({'head': heads[0]}).encode())
        write(older / 'bank/default/Module.v', b'source')
        write(older / 'bank/default/Module.vo')
        newest = self.agents / 'a/bank-new'
        write(newest / 'READY.json', json.dumps({'head': heads[1]}).encode())
        write(newest / 'bank/default/Module.vo')
        build_bank = write(self.root / '_build/banks' / heads[0] / 'default/Module.vo')
        plan, log = self.plan_and_apply(self.janitor(), self.live())
        self.assertFalse((older / 'bank').exists())
        self.assertTrue((older / 'READY.json').exists())
        self.assertFalse(build_bank.parent.parent.exists())
        self.assertTrue((newest / 'bank/default/Module.vo').exists())
        self.assertIn('remove-tree', log)
        reasons = {row['path']: row['reason'] for row in plan['rows']}
        self.assertEqual(reasons[str(newest)], 'bank of the newest main commit')

    def repository(self, count):
        self.root.mkdir(parents=True, exist_ok=True)
        environment = dict(os.environ, GIT_AUTHOR_NAME='t', GIT_AUTHOR_EMAIL='t@t',
                           GIT_COMMITTER_NAME='t', GIT_COMMITTER_EMAIL='t@t')

        def git(*arguments):
            return subprocess.run(['git', '-C', str(self.root), *arguments], check=True,
                                  capture_output=True, text=True, env=environment).stdout
        git('init', '-q', '-b', 'main')
        heads = []
        for index in range(count):
            git('commit', '-q', '--allow-empty', '-m', str(index))
            heads.append(git('rev-parse', 'HEAD').strip())
        git('update-ref', 'refs/remotes/origin/main', heads[-1])
        return heads


class Commands(JanitorTree):
    def test_dry_run_deletes_nothing_and_writes_budget_and_plan(self):
        write(self.agents / 'a/old/Module.vo')
        with patch.object(J, 'base_root', return_value=self.root), patch('builtins.print'):
            J.main(['--jobs', '1'])
        self.assertTrue((self.agents / 'a/old/Module.vo').exists())
        budget = json.loads((self.root / '_build/BUDGET.json').read_text())
        self.assertEqual(budget['schema'], 'zesu.build-budget.v1')
        self.assertIn('a', budget['agents'])
        self.assertTrue(list((self.root / '_build/janitor').glob('plan-*-dry-run.json')))
        self.assertIn('dry-run', (self.root / '_build/janitor/janitor.log').read_text())

    def test_apply_logs_every_deleted_file(self):
        run = self.agents / 'a/old'
        write(run / 'Module.vo')
        with patch.object(J, 'base_root', return_value=self.root), \
                patch.object(J.Janitor, '__init__', self.clocked_init()), patch('builtins.print'):
            J.main(['--jobs', '1', '--apply'])
        self.assertFalse((run / 'Module.vo').exists())
        [log] = (self.root / '_build/janitor').glob('deleted-*.tsv.gz')
        with gzip.open(log, 'rt') as stream:
            self.assertIn(str(run / 'Module.vo'), stream.read())

    def clocked_init(self):
        original = J.Janitor.__init__
        now = self.now

        def init(janitor, root, **options):
            options['now'] = now
            original(janitor, root, **options)
        return init

    def budget(self, over=True, protected=False):
        path = write(self.root / '_build/BUDGET.json', json.dumps({
            'measured_at': '2026-11-08T00:00:00Z',
            'agents': {'a': {'unique_bytes': 50 * J.GB, 'budget_bytes': 40 * J.GB,
                             'over': over, 'protected': protected}}}).encode())
        return {'ZESU_BUILD_BUDGET': str(path)}

    def admit(self, environment):
        with patch('sys.stderr', new_callable=io.StringIO) as error:
            status = J.admit(argparse.Namespace(root=None), environment)
        return status, error.getvalue()

    def test_admission_refuses_an_agent_over_budget_and_names_the_janitor(self):
        environment = self.budget()
        environment['AGENT_BUILD_DIR'] = str(self.agents / 'a/run7')
        status, message = self.admit(environment)
        self.assertEqual(status, 3)
        self.assertIn('make janitor', message)
        self.assertIn('agent a', message)
        status, _ = self.admit(dict(self.budget(), COORD_AGENT='a'))
        self.assertEqual(status, 3)

    def test_admission_allows_under_budget_protected_unknown_and_missing(self):
        self.assertEqual(self.admit(dict(self.budget(over=False), COORD_AGENT='a'))[0], 0)
        self.assertEqual(self.admit(dict(self.budget(protected=True), COORD_AGENT='a'))[0], 0)
        self.assertEqual(self.admit(dict(self.budget(), COORD_AGENT='b'))[0], 0)
        self.assertEqual(self.admit(self.budget())[0], 0)
        missing = {'ZESU_BUILD_BUDGET': str(self.root / 'none.json'), 'COORD_AGENT': 'a'}
        self.assertEqual(self.admit(missing)[0], 0)

    def test_resource_guard_refuses_a_new_run_over_budget(self):
        base = Path(self.temp.name)
        environment = {name: value for name, value in os.environ.items()
                       if not name.startswith('ZESU_')}
        environment.update(self.budget(), ZESU_BUILD_AGENT='a',
                           ZESU_GATE_LOCK=str(base / 'lock'), ZESU_GUARD_STATE=str(base / 'state'),
                           ZESU_RUN_REGISTRY=str(base / 'registry'),
                           ZESU_RAMP_FILE=str(base / 'ramp'),
                           ZESU_CANONICAL_LEDGER=str(write(base / 'LEDGER.json', b'{}')))
        result = subprocess.run([str(TOOLS / 'resource_guard.sh'), 'batch', 'fixture', '--',
                                 'true'], env=environment, capture_output=True, text=True,
                                timeout=60)
        self.assertEqual(result.returncode, 3, result.stderr)
        self.assertIn('make janitor', result.stderr)
        self.assertFalse((base / 'registry').exists())

    def test_branch_items_match_item_json_or_name_and_skip_orch(self):
        tied = write(self.agents / 'a/run9/ITEM.json', json.dumps({'branch': 'w/feature'}).encode())
        named = write(self.agents / 'b/feature/Module.vo')
        other = write(self.agents / 'b/feature-x/ITEM.json', json.dumps({'branch': 'other'}).encode())
        claimed = write(self.agents / 'c/feature/ITEM.json', json.dumps({'branch': 'other'}).encode())
        orch = write(self.agents / 'orch/w-feature/Module.vo')
        args = argparse.Namespace(
            root=str(self.root), log_dir=None, branch='w/feature', delete=True)
        with patch.object(J.LivePaths, 'scan', return_value=J.LivePaths([], {})), \
                patch('builtins.print') as output:
            J.branch_items(args)
        printed = '\n'.join(call.args[0] for call in output.call_args_list)
        self.assertFalse(tied.parent.exists())
        self.assertFalse(named.parent.exists())
        self.assertTrue(other.exists())
        self.assertTrue(claimed.exists())
        self.assertTrue(orch.exists())
        self.assertIn('protected agent', printed)
        self.assertIn('removed run dir', printed)

    def ledger(self, *receipts):
        ledger = write(self.root / 'LEDGER.json', json.dumps({'released_region_claims': {
            str(index): {'bytes': 1, 'receipt': str(receipt), 'sha256': '0'}
            for index, receipt in enumerate(receipts)}}).encode())
        return patch.dict(os.environ, {'ZESU_CANONICAL_LEDGER': str(ledger)})

    def test_ledger_receipts_keep_their_worktree_and_run_dir(self):
        # A worktree removal deleted the 6ae0 release receipt on 2026-11-12; every admission crashed.
        worktree = self.root / '.worktrees/w'
        receipt = write(worktree / '_build/native-cut/6AE0-CLAIM-RELEASE-v1/REPORT.json')
        run_receipt = write(self.agents / 'a/run9/RELEASE.json')
        write(self.agents / 'a/run9/ITEM.json', json.dumps({'branch': 'w/feature'}).encode())
        with self.ledger(receipt, run_receipt), \
                patch.object(J.LivePaths, 'scan', return_value=J.LivePaths([], {})), \
                patch('builtins.print') as output:
            self.assertEqual(J.in_use(argparse.Namespace(root=str(self.root), paths=[str(worktree)])), 0)
            self.assertEqual(J.in_use(argparse.Namespace(root=str(self.root),
                                                         paths=[str(self.root / '.worktrees/x')])), 1)
            J.branch_items(argparse.Namespace(root=str(self.root), log_dir=None, branch='w/feature',
                                              delete=True))
        printed = '\n'.join(call.args[0] for call in output.call_args_list)
        self.assertIn('the admission ledger names receipt ' + str(receipt), printed)
        self.assertIn('kept: admission ledger receipt ' + str(run_receipt), printed)
        self.assertTrue(run_receipt.exists())


if __name__ == '__main__':
    unittest.main()
