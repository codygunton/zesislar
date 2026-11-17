"""Launch long jobs outside the caller's tree, refuse unsafe kills, and ledger signal deaths."""

import json
import os
from pathlib import Path
import re
import shutil
import signal
import subprocess
import sys
import tempfile
import time
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parent))
import kill_scan
import module_memory
import run_registry as R

REGISTRY = str(Path(R.__file__).resolve())
BG = str(Path(__file__).with_name('bg'))
# Waits for an event, never a speed requirement (as in test_run_registry.py).
EVENT_CEILING_SECONDS = 120
# Built from fragments, so this file passes the committed-script scan.
PARENT_KILL = 'p' + 'kill -P $' + '$'
PGREP_KILL = 'kill $(p' + 'grep -f qseq.sh)'
RECORDER = """#!/usr/bin/env python3
import json, os, sys
with open(os.environ['TEST_SYSTEMD_LOG'], 'a') as stream:
    stream.write(json.dumps([os.path.basename(sys.argv[0])] + sys.argv[1:]) + '\\n')
if os.path.basename(sys.argv[0]) == 'systemd-run':
    tail = sys.argv[sys.argv.index('--') + 1:]
    os.execvp(tail[0], tail)
"""


def ancestors(pid):
    found = []
    while pid > 1:
        current = R.identity(pid)
        if current is None:
            break
        pid = current['ppid']
        found.append(pid)
    return found


class Fixture(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.store = self.root / 'registry'
        self.fences = self.root / 'fence-kills.jsonl'
        self.registry = R.Registry(self.store, fence_ledger=self.fences)
        bin_dir = self.root / 'bin'
        bin_dir.mkdir()
        for name in ('systemd-run', 'systemctl'):
            (bin_dir / name).write_text(RECORDER)
            (bin_dir / name).chmod(0o755)
        self.systemd_log = self.root / 'systemd.jsonl'
        self.environment = {**os.environ, 'PATH': f"{bin_dir}:{os.environ['PATH']}",
                            'TEST_SYSTEMD_LOG': str(self.systemd_log), 'ZESU_RUN_REGISTRY': str(self.store),
                            'ZESU_GUARD_STATE': str(self.root)}
        for key in ('ZESU_RUN_ID', 'ZESU_OWNER', 'ZESU_PARENT_RUN_ID'):
            self.environment.pop(key, None)
        self.processes = []
        self.addCleanup(self.close)

    def close(self):
        for row in self.registry.active():
            self.cli('stop', row['id'])
        for process in self.processes:
            if process.poll() is None:
                process.kill()
            process.wait(timeout=EVENT_CEILING_SECONDS)

    def cli(self, *arguments, cwd=None):
        return subprocess.run([sys.executable, '-B', REGISTRY, '--store', str(self.store), *arguments],
                              cwd=cwd or self.root, env=self.environment, capture_output=True, text=True,
                              timeout=EVENT_CEILING_SECONDS)

    def systemd_calls(self):
        if not self.systemd_log.exists():
            return []
        return [json.loads(line) for line in self.systemd_log.read_text().splitlines()]

    def wait_for(self, predicate):
        deadline = time.monotonic() + EVENT_CEILING_SECONDS
        while time.monotonic() < deadline:
            result = predicate()
            if result:
                return result
            time.sleep(0.02)
        self.fail('The disposable fixture did not reach its expected state.')

    def run_fixture(self, run_id, code, *options):
        process = subprocess.Popen(
            [sys.executable, '-B', REGISTRY, '--store', str(self.store), 'run', '--id', run_id,
             '--kind', 'fixture', '--owner', 'test', *options, '--', sys.executable, '-c', code],
            env=self.environment, cwd=self.root, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
        self.processes.append(process)
        return process


class LaunchTests(Fixture):
    def test_launch_runs_outside_the_callers_process_tree_and_stop_ends_its_unit(self):
        result = self.cli('launch', '--name', 'watch', '--owner', 'tester', '--',
                          sys.executable, '-c', 'import time; print("started", flush=True); time.sleep(60)')
        self.assertEqual(result.returncode, 0, result.stderr)
        run_id = result.stdout.strip()
        row = self.registry.read_run(run_id)
        unit = f'zesubg-{run_id}.scope'
        self.assertTrue(run_id.startswith('tester-watch-'), run_id)
        self.assertEqual((row['owner'], row['kind'], row['unit'], row['run_dir'], row['log']),
                         ('tester', 'bg', unit, str(self.root), str(self.root / 'watch.log')))
        self.assertEqual(row['command'][-1], 'import time; print("started", flush=True); time.sleep(60)')
        launch = self.systemd_calls()[0]
        self.assertEqual(launch[:7], ['systemd-run', '--user', '--scope', '--quiet', '--collect',
                                      '--expand-environment=no', f'--unit={unit}'])
        mine = {R.actor_key(actor) for actor in R.descendants([R.identity(os.getpid())])}
        for actor in [row['scheduler']] + row['jobs']:
            self.assertTrue(R.live(actor))
            self.assertNotIn(R.actor_key(actor), mine)
            self.assertNotIn(os.getpid(), ancestors(actor['pid']))
        self.wait_for(lambda: 'started' in (self.root / 'watch.log').read_text())
        stopped = self.cli('stop', run_id)
        self.assertEqual(stopped.returncode, 0, stopped.stderr)
        row = self.registry.read_run(run_id)
        self.assertEqual(row['status'], 'stopped')
        self.assertFalse(any(R.live(actor) for actor in [row['scheduler']] + row['jobs']))
        self.assertIn(['systemctl', '--user', 'stop', unit], self.systemd_calls())
        self.assertEqual(self.registry.reap(), [])

    def test_launched_job_does_not_inherit_the_callers_run_id(self):
        self.environment['ZESU_RUN_ID'] = 'outer-run'
        result = self.cli('launch', '--name', 'env', '--owner', 'tester', '--', sys.executable, '-c',
                          'import os; print(*(os.environ.get(key) for key in '
                          '("ZESU_RUN_ID", "ZESU_PARENT_RUN_ID", "ZESU_OWNER")))')
        self.assertEqual(result.returncode, 0, result.stderr)
        run_id = result.stdout.strip()
        self.wait_for(lambda: self.registry.read_run(run_id)['status'] == 'completed')
        self.assertEqual((self.root / 'env.log').read_text().split(), ['None', run_id, 'tester'])

    def test_guard_run_inside_a_bg_run_takes_its_owner_parent_and_records_worktree_and_module(self):
        checkout = self.root / 'checkout'
        checkout.mkdir()
        subprocess.run(['git', 'init', '-q', '-b', 'lane-branch', str(checkout)], check=True,
                       timeout=EVENT_CEILING_SECONDS)
        (checkout / 'column.py').write_text('pass\n')
        guard = checkout / 'guard.sh'
        guard.write_text('#!/usr/bin/env bash\nexit 0\n')
        guard.chmod(0o755)
        child = [sys.executable, '-B', REGISTRY, '--store', str(self.store), 'run', '--id', 'child',
                 '--kind', 'stock-batch', '--', str(guard), 'batch', 'block-0514', '--', sys.executable, 'column.py']
        result = self.cli('launch', '--name', 'lane', '--owner', 'tester', '--dir', str(checkout), '--', *child)
        self.assertEqual(result.returncode, 0, result.stderr)
        parent = result.stdout.strip()
        self.wait_for(lambda: self.registry.contains('child')
                      and self.registry.read_run('child')['status'] == 'completed')
        row = self.registry.read_run('child')
        self.assertEqual((row['owner'], row['parent_run_id'], row['worktree'], row['modules']),
                         ('tester', parent, str(checkout.resolve()), [str((checkout / 'column.py').resolve())]))
        listed = self.cli('list')
        self.assertRegex(listed.stdout, rf'(?m)^child stock-batch tester completed .* '
                                        rf'worktree={re.escape(str(checkout.resolve()))} module=column\.py$')

    def test_bg_wrapper_launches_lists_and_stops(self):
        result = subprocess.run([BG, 'loop', 'sleep', '60'], cwd=self.root, env=self.environment,
                                capture_output=True, text=True, timeout=EVENT_CEILING_SECONDS)
        self.assertEqual(result.returncode, 0, result.stderr)
        run_id = result.stdout.strip()
        listed = subprocess.run([BG, 'list'], env=self.environment, capture_output=True, text=True,
                                timeout=EVENT_CEILING_SECONDS)
        self.assertIn(run_id, listed.stdout)
        stopped = subprocess.run([BG, 'stop', run_id], env=self.environment, capture_output=True, text=True,
                                 timeout=EVENT_CEILING_SECONDS)
        self.assertEqual(stopped.returncode, 0, stopped.stderr)
        self.assertEqual(self.registry.read_run(run_id)['status'], 'stopped')

    def test_launch_refuses_a_script_that_kills_by_parent_pid(self):
        script = self.root / 'watch.sh'
        script.write_text('#!/usr/bin/env bash\n# stop old copies first\n' + PARENT_KILL + '\nsleep 60\n')
        result = self.cli('launch', '--name', 'watch', '--', 'bash', 'watch.sh')
        self.assertEqual(result.returncode, R.LAUNCH_REFUSED, result.stderr)
        self.assertIn(f'{script}:3: {PARENT_KILL}', result.stderr)
        self.assertIn('Safe form', result.stderr)
        self.assertEqual(self.systemd_calls(), [])
        self.assertEqual(self.registry.read()['runs'], {})

    def test_launch_refuses_a_script_that_logs_a_false_exit_code(self):
        script = self.root / 'lane.sh'
        script.write_text(FALSE_RC_SCRIPT)
        result = self.cli('launch', '--name', 'lane', '--', 'bash', 'lane.sh')
        self.assertEqual(result.returncode, R.LAUNCH_REFUSED, result.stderr)
        self.assertIn(f'refused: {script}:3: ', result.stderr)
        self.assertIn('rc=$? on its own line right after the command', result.stderr)
        self.assertEqual(self.systemd_calls(), [])
        self.assertEqual(self.registry.read()['runs'], {})

    def test_launch_refuses_an_unsafe_kill_in_a_queue_script_the_command_starts(self):
        (self.root / 'q').mkdir()
        (self.root / 'q' / 'xrun.sh').write_text('#!/bin/bash\n' + PGREP_KILL + '\n')
        (self.root / 'q' / 'queue.sh').write_text('#!/bin/bash\nhere=$(dirname "$0")\n"$here/xrun.sh" 0144\n')
        result = self.cli('launch', '--name', 'queue', '--', 'bash', 'q/queue.sh')
        self.assertEqual(result.returncode, R.LAUNCH_REFUSED, result.stderr)
        self.assertIn(f"{self.root / 'q' / 'xrun.sh'}:2:", result.stderr)
        self.assertEqual(self.systemd_calls(), [])

    def test_launch_refuses_an_inline_unsafe_kill(self):
        result = self.cli('launch', '--name', 'inline', '--', 'bash', '-c', 'sleep 5; ' + PARENT_KILL)
        self.assertEqual(result.returncode, R.LAUNCH_REFUSED, result.stderr)
        self.assertIn('<command line>:3:', result.stderr)

    @unittest.skipUnless(os.environ.get('ZESU_RUN_LAUNCH_LIVE') == '1', 'opt-in live systemd scope')
    def test_live_launch_holds_the_job_in_its_own_user_scope(self):
        self.environment['PATH'] = os.environ['PATH']
        # systemd-run expands variables by default and would run `sleep 60; echo $ /home/...`.
        script = 'sleep 60; echo $$ ${HOME}'
        result = self.cli('launch', '--name', 'live', '--owner', 'tester', '--', 'sh', '-c', script)
        self.assertEqual(result.returncode, 0, result.stderr)
        run_id = result.stdout.strip()
        row = self.registry.read_run(run_id)
        self.assertEqual(row['command'], ['sh', '-c', script])
        cgroup = Path(f"/proc/{row['jobs'][0]['pid']}/cgroup").read_text()
        self.assertTrue(cgroup.strip().endswith('/' + row['unit']), cgroup)
        self.assertNotIn(os.getpid(), ancestors(row['scheduler']['pid']))
        self.assertEqual(self.cli('stop', run_id).returncode, 0)
        state = subprocess.run(['systemctl', '--user', 'is-active', row['unit']], capture_output=True, text=True)
        self.assertNotEqual(state.stdout.strip(), 'active')


class OwnerTests(Fixture):
    def test_owner_order_is_env_then_parent_run_then_branch_then_user(self):
        checkout = self.root / 'checkout'
        checkout.mkdir()
        subprocess.run(['git', 'init', '-q', '-b', 'lane-branch', str(checkout)], check=True,
                       timeout=EVENT_CEILING_SECONDS)
        sleeper = subprocess.Popen([sys.executable, '-c', 'import time; time.sleep(60)'])
        self.processes.append(sleeper)
        self.registry.register('bg-parent', 'bg', 'parent-owner', self.wait_for(lambda: R.identity(sleeper.pid)), [])
        cases = [({'ZESU_OWNER': 'explicit', 'ZESU_PARENT_RUN_ID': 'bg-parent'}, checkout, 'explicit'),
                 ({'ZESU_PARENT_RUN_ID': 'bg-parent'}, checkout, 'parent-owner'),
                 ({'ZESU_PARENT_RUN_ID': 'missing'}, checkout, 'lane-branch'),
                 ({}, checkout, 'lane-branch'),
                 ({}, self.root, R.user_name())]
        for extra, cwd, owner in cases:
            with patch.dict(os.environ, extra):
                for key in {'ZESU_OWNER', 'ZESU_PARENT_RUN_ID'} - set(extra):
                    os.environ.pop(key, None)
                self.assertEqual(R.resolve_owner(self.registry, cwd), owner, extra)


class DuplicateLaunchTests(Fixture):
    def launch(self, name, *options):
        return self.cli('launch', '--name', name, '--owner', 'tester', *options, '--',
                        sys.executable, '-c', 'import time; time.sleep(60)')

    def assert_notices_are_not_refusals(self, stderr):
        for line in stderr.splitlines():
            if line.startswith('notice:'):
                self.assertNotIn('refused:', line)

    def test_retry_with_the_same_owner_and_name_is_refused_until_the_first_ends(self):
        first = self.launch('retry')
        self.assertEqual(first.returncode, 0, first.stderr)
        self.assertTrue(first.stderr.startswith('notice: '), first.stderr)
        self.assert_notices_are_not_refusals(first.stderr)
        run_id = first.stdout.strip()
        calls = len(self.systemd_calls())
        second = self.launch('retry')
        self.assertEqual(second.returncode, R.DUPLICATE_REFUSED, second.stderr)
        self.assertEqual(second.stdout, '')
        self.assertTrue(second.stderr.startswith('refused: duplicate launch: '), second.stderr)
        self.assertIn(f'live run {run_id}', second.stderr)
        self.assertIn(f'tools/bg stop {run_id}', second.stderr)
        self.assertEqual(len(self.systemd_calls()), calls)
        self.assertEqual(list(self.registry.read()['runs']), [run_id])
        # Another name is another run.
        other = self.launch('other')
        self.assertEqual(other.returncode, 0, other.stderr)
        self.assertEqual(self.cli('stop', run_id).returncode, 0)
        again = self.launch('retry')
        self.assertEqual(again.returncode, 0, again.stderr)
        self.assert_notices_are_not_refusals(again.stderr)

    def test_bg_refuses_a_live_duplicate_with_exit_6_and_allow_duplicate_overrides(self):
        def bg(*arguments):
            return subprocess.run([BG, '--owner', 'tester', *arguments, 'loop', 'sleep', '60'], cwd=self.root,
                                  env=self.environment, capture_output=True, text=True,
                                  timeout=EVENT_CEILING_SECONDS)
        first = bg()
        self.assertEqual(first.returncode, 0, first.stderr)
        second = bg()
        self.assertEqual(second.returncode, 6, second.stderr)
        self.assertIn(first.stdout.strip(), second.stderr)
        forced = bg('--allow-duplicate')
        self.assertEqual(forced.returncode, 0, forced.stderr)
        self.assertEqual(len(self.registry.active()), 2)

    def stock_batch(self, run_id, name, *options, wait=False):
        # The registry derives a stock run's identity from the guard command it runs.
        command = [sys.executable, '-B', REGISTRY, '--store', str(self.store), 'run', '--id', run_id,
                   '--kind', 'stock-batch', '--owner', 'tester', *options, '--',
                   str(self.root / 'guard.sh'), 'batch', name, '--', sys.executable, 'column.py']
        if wait:
            return subprocess.run(command, cwd=self.root, env=self.environment, capture_output=True, text=True,
                                  timeout=EVENT_CEILING_SECONDS)
        process = subprocess.Popen(command, cwd=self.root, env=self.environment,
                                   stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
        self.processes.append(process)
        self.wait_for(lambda: self.registry.contains(run_id) and self.registry.read_run(run_id)['jobs'])
        return process

    def test_guard_batch_identity_is_owner_name_caller_file_and_bank_dir(self):
        (self.root / 'column.py').write_text('pass\n')
        guard = self.root / 'guard.sh'
        guard.write_text('#!/usr/bin/env bash\n[ -e hold ] && exec sleep 60\nexit 0\n')
        guard.chmod(0o755)
        (self.root / 'hold').write_text('')
        first = self.stock_batch('first', 'block-0514')
        self.assertEqual(json.loads(self.registry.read_run('first')['identity']),
                         ['guard', 'tester', 'block-0514', [str(self.root / 'column.py')],
                          str(self.root.resolve())])
        # A retry script relaunches the same name, caller file and bank dir.
        refused = self.stock_batch('second', 'block-0514', wait=True)
        self.assertEqual(refused.returncode, R.DUPLICATE_REFUSED, refused.stderr)
        self.assertTrue(refused.stderr.startswith('refused: duplicate launch: live run first '), refused.stderr)
        self.assertIn('tools/bg stop first', refused.stderr)
        self.assertFalse(self.registry.contains('second'))
        (self.root / 'hold').unlink()
        other = self.stock_batch('other', 'block-0244', wait=True)
        self.assertEqual(other.returncode, 0, other.stderr)
        forced = self.stock_batch('forced', 'block-0514', '--allow-duplicate', wait=True)
        self.assertEqual(forced.returncode, 0, forced.stderr)
        self.assertEqual(self.cli('stop', 'first').returncode, 0)
        first.wait(timeout=EVENT_CEILING_SECONDS)
        again = self.stock_batch('third', 'block-0514', wait=True)
        self.assertEqual(again.returncode, 0, again.stderr)


class SignalDeathTests(Fixture):
    def entries(self):
        if not self.registry.signal_ledger.exists():
            return []
        return [json.loads(line) for line in self.registry.signal_ledger.read_text().splitlines()]

    def test_signal_death_without_stop_is_ledgered_once(self):
        process = self.run_fixture('killed', 'import os, signal, time; os.kill(os.getpid(), signal.SIGTERM); time.sleep(9)',
                                   '--unit', 'zesubg-killed.scope')
        process.wait(timeout=EVENT_CEILING_SECONDS)
        reaped = self.registry.reap()
        self.assertEqual(len(reaped), 1)
        entry = reaped[0]
        self.assertEqual((entry['run_id'], entry['signal'], entry['signal_name'], entry['unit'], entry['cause'],
                          entry['evidence']),
                         ('killed', signal.SIGTERM, 'SIGTERM', 'zesubg-killed.scope', 'unknown', 'signal'))
        self.assertRegex(entry['utc'], r'^\d{4}-\d\d-\d\dT\d\d:\d\d:\d\dZ$')
        self.assertEqual(self.entries(), [entry])
        self.assertEqual(self.registry.reap(), [])
        self.assertEqual(len(self.entries()), 1)

    def test_signal_to_the_scheduler_is_ledgered(self):
        process = self.run_fixture('interrupted', 'import time; time.sleep(60)')
        self.wait_for(lambda: self.registry.contains('interrupted') and self.registry.read_run('interrupted')['jobs'])
        process.send_signal(signal.SIGTERM)
        process.wait(timeout=EVENT_CEILING_SECONDS)
        [entry] = self.registry.reap()
        self.assertEqual((entry['run_id'], entry['signal_name']), ('interrupted', 'SIGTERM'))

    def test_vanished_scheduler_is_ledgered(self):
        sleeper = subprocess.Popen([sys.executable, '-c', 'import time; time.sleep(60)'])
        self.processes.append(sleeper)
        actor = self.wait_for(lambda: R.identity(sleeper.pid))
        self.registry.register('vanished', 'fixture', 'test', actor, [])
        sleeper.kill()
        sleeper.wait(timeout=EVENT_CEILING_SECONDS)
        [entry] = self.registry.reap()
        self.assertEqual((entry['run_id'], entry['signal'], entry['evidence']),
                         ('vanished', None, 'scheduler ended without a record'))

    def test_stopped_and_normally_failed_runs_are_not_ledgered(self):
        failed = self.run_fixture('failed', 'raise SystemExit(1)')
        failed.wait(timeout=EVENT_CEILING_SECONDS)
        self.run_fixture('stopped', 'import time; time.sleep(60)')
        self.wait_for(lambda: self.registry.contains('stopped') and self.registry.read_run('stopped')['jobs'])
        self.registry.stop('stopped', grace=1.0)
        self.assertEqual(self.registry.reap(), [])
        self.assertEqual(self.entries(), [])

    def test_fence_kill_of_the_run_is_labelled_memory_fence(self):
        (self.root / 'Probe.v').write_text('Lemma probe : True. Proof. exact I. Qed.\n')
        with patch.dict(os.environ, {'ZESU_RUN_ID': 'fenced'}):
            module_memory.record_fence_kill(self.fences, 'zesudet-probe.scope', 16 * module_memory.GIB,
                                            ['coqc', 'Probe.v'], self.root)
        process = self.run_fixture('fenced', 'raise SystemExit(143)')
        process.wait(timeout=EVENT_CEILING_SECONDS)
        [entry] = self.registry.reap()
        self.assertEqual((entry['cause'], entry['fence_unit'], entry['signal_name'], entry['evidence']),
                         ('memory fence', 'zesudet-probe.scope', 'SIGTERM', 'exit status'))

    def test_watchdog_posts_each_new_entry_to_status_once(self):
        status = self.root / 'STATUS.md'
        self.assertEqual(R.watchdog(self.registry, status), [])
        process = self.run_fixture('posted', 'import os, signal; os.kill(os.getpid(), signal.SIGKILL)')
        process.wait(timeout=EVENT_CEILING_SECONDS)
        [message] = R.watchdog(self.registry, status)
        self.assertIn('run posted (owner test, kind fixture, unit none, worktree none, module none) '
                      'ended by SIGKILL from unknown', message)
        self.assertIn('cause: unknown', message)
        self.assertEqual(status.read_text(), message + '\n')
        self.assertEqual(R.watchdog(self.registry, status), [])
        result = self.cli('watchdog', '--status', str(status))
        self.assertEqual((result.returncode, result.stdout), (0, ''), result.stderr)

    def test_sender_of_a_signal_to_the_scheduler_is_recorded(self):
        process = self.run_fixture('sent', 'import time; time.sleep(60)')
        self.wait_for(lambda: self.registry.contains('sent') and self.registry.read_run('sent')['jobs'])
        sender = subprocess.Popen([sys.executable, '-c', f'import os, signal, time; '
                                   f'os.kill({process.pid}, signal.SIGTERM); time.sleep(60)'])
        self.processes.append(sender)
        process.wait(timeout=EVENT_CEILING_SECONDS)
        [entry] = self.registry.reap()
        self.assertEqual(entry['signal_name'], 'SIGTERM')
        self.assertTrue(entry['sender'].startswith(f'pid {sender.pid} ('), entry['sender'])
        self.assertIn('os.kill', entry['sender'])
        self.assertEqual(entry['cause'], 'unknown')

    def test_systemd_sender_names_the_units_stop_job(self):
        bin_dir = self.root / 'fake-systemd'
        bin_dir.mkdir()
        (bin_dir / 'systemctl').write_text('#!/bin/sh\necho "4242 zesubg-x.scope stop running"\n'
                                           'echo "4243 other.scope stop running"\n')
        (bin_dir / 'systemctl').chmod(0o755)
        (bin_dir / 'systemd').symlink_to(shutil.which('sleep'))
        manager = subprocess.Popen([str(bin_dir / 'systemd'), '60'])
        self.processes.append(manager)
        self.wait_for(lambda: Path(f'/proc/{manager.pid}/comm').read_text().strip() == 'systemd')
        info = type('Info', (), {'si_pid': manager.pid})()
        with patch.dict(os.environ, {'PATH': f"{bin_dir}:{os.environ['PATH']}"}), \
                patch.object(R, 'own_unit', return_value='zesubg-x.scope'):
            self.assertEqual(R.signal_sender(info), 'systemd user stop job 4242 for zesubg-x.scope')
        with patch.object(R, 'own_unit', return_value='gone.scope'), patch.object(R, 'stop_job', return_value=None):
            self.assertEqual(R.signal_sender(info),
                             'systemd user manager stopping gone.scope (stop job unknown)')
        self.assertEqual(R.signal_sender(type('Info', (), {'si_pid': 0})()), 'unknown')

    def test_child_of_a_stopped_bg_run_is_labelled_parent_stopped_and_not_posted(self):
        status = self.root / 'STATUS.md'
        self.assertEqual(R.watchdog(self.registry, status), [])
        child = [sys.executable, '-B', REGISTRY, '--store', str(self.store), 'run', '--id', 'child',
                 '--kind', 'fixture', '--', sys.executable, '-c', 'import time; time.sleep(60)']
        result = self.cli('launch', '--name', 'lane', '--owner', 'tester', '--', *child)
        self.assertEqual(result.returncode, 0, result.stderr)
        parent = result.stdout.strip()
        self.wait_for(lambda: self.registry.contains('child') and self.registry.read_run('child')['jobs'])
        self.assertEqual(self.cli('stop', parent).returncode, 0)
        self.wait_for(lambda: self.registry.read_run('child')['status'] != 'running')
        [entry] = self.registry.reap()
        self.assertEqual((entry['run_id'], entry['cause'], entry['parent_run_id'], entry['owner']),
                         ('child', 'parent stopped', parent, 'tester'))
        self.assertEqual(R.watchdog(self.registry, status), [])
        self.assertFalse(status.exists())


class WorkloadSliceTests(Fixture):
    def test_missing_workload_slice_is_posted_once_and_again_after_it_returns(self):
        status = self.root / 'STATUS.md'
        cgroups = self.root / 'cgroup'
        uid = os.getuid()
        parent = cgroups / 'user.slice' / f'user-{uid}.slice' / f'user@{uid}.service' / 'zesuworkloads.slice'
        [message] = R.workload_slice_report(self.registry, status, cgroups, uid)
        self.assertIn(f'workload slice zesuworkloads.slice is missing ({parent})', message)
        self.assertIn('make install-workload-slice', message)
        self.assertEqual(status.read_text(), message + '\n')
        self.assertEqual(R.workload_slice_report(self.registry, status, cgroups, uid), [])
        parent.mkdir(parents=True)
        (parent / 'memory.max').write_text('120259084288\n')
        self.assertEqual(R.workload_slice_report(self.registry, status, cgroups, uid), [])
        (parent / 'memory.max').unlink()
        self.assertEqual(len(R.workload_slice_report(self.registry, status, cgroups, uid)), 1)
        self.assertEqual(len(status.read_text().splitlines()), 2)


class FollowMainTests(Fixture):
    def git(self, checkout, *arguments, check=True):
        result = subprocess.run(['git', '-C', str(checkout), *arguments], env=self.environment,
                                capture_output=True, text=True, timeout=EVENT_CEILING_SECONDS)
        if check:
            self.assertEqual(result.returncode, 0, result.stderr)
        return result.stdout.strip()

    def setUp(self):
        super().setUp()
        self.environment.update(GIT_AUTHOR_NAME='t', GIT_AUTHOR_EMAIL='t@t', GIT_COMMITTER_NAME='t',
                                GIT_COMMITTER_EMAIL='t@t')
        self.origin = self.root / 'origin.git'
        self.writer = self.root / 'writer'
        self.tools = self.root / 'ops-tools'
        self.status = self.root / 'STATUS.md'
        self.git(self.root, 'init', '--quiet', '--bare', '--initial-branch=main', str(self.origin))
        self.git(self.root, 'clone', '--quiet', str(self.origin), str(self.writer))
        self.commit('one')
        self.git(self.root, 'clone', '--quiet', str(self.origin), str(self.tools))
        self.git(self.tools, 'checkout', '--quiet', '--detach')

    def commit(self, text):
        (self.writer / 'tool.txt').write_text(text + '\n')
        self.git(self.writer, 'add', 'tool.txt')
        self.git(self.writer, 'commit', '--quiet', '-m', text)
        self.git(self.writer, 'push', '--quiet', 'origin', 'HEAD:main')
        return self.git(self.writer, 'rev-parse', 'HEAD')

    def follow(self, returncode=0):
        result = self.cli('watchdog', '--follow-main', str(self.tools), '--status', str(self.status))
        self.assertEqual(result.returncode, returncode, result.stderr)
        return result.stdout

    def test_clean_checkout_fast_forwards_to_origin_main_and_logs_the_move(self):
        self.assertEqual(self.follow(), '')
        (self.tools / 'bg-run.log').write_text('untracked logs do not hold the checkout\n')
        old = self.git(self.tools, 'rev-parse', 'HEAD')
        new = self.commit('two')
        output = self.follow()
        self.assertEqual(self.git(self.tools, 'rev-parse', 'HEAD'), new)
        self.assertEqual(self.git(self.tools, 'symbolic-ref', '-q', 'HEAD', check=False), '')
        self.assertIn(f'moved {self.tools} from {old[:12]} to origin/main {new[:12]}', output)
        self.assertIn(f'from {old[:12]} to origin/main {new[:12]}', (self.store / 'follow-main.log').read_text())
        self.assertFalse(self.status.exists())
        self.assertEqual(self.follow(), '')

    def test_dirty_checkout_stays_and_is_posted_to_status_once(self):
        old = self.git(self.tools, 'rev-parse', 'HEAD')
        (self.tools / 'tool.txt').write_text('local edit\n')
        self.commit('two')
        first = self.follow(1)
        self.assertIn('held at', first)
        self.assertEqual(self.git(self.tools, 'rev-parse', 'HEAD'), old)
        posted = self.status.read_text().splitlines()
        self.assertEqual(len(posted), 1, posted)
        self.assertIn(f'tools checkout {self.tools} no longer follows main: it has uncommitted changes', posted[0])
        self.assertIn('held at', self.follow(1))
        self.assertEqual(self.status.read_text().splitlines(), posted)
        self.git(self.tools, 'checkout', '--quiet', '--', 'tool.txt')
        new = self.commit('three')
        self.assertIn('moved', self.follow())
        self.assertEqual(self.git(self.tools, 'rev-parse', 'HEAD'), new)
        (self.tools / 'tool.txt').write_text('dirty again\n')
        self.commit('four')
        self.follow(1)
        self.assertEqual(len(self.status.read_text().splitlines()), 2)

    def test_local_commits_hold_the_checkout(self):
        (self.tools / 'tool.txt').write_text('local commit\n')
        self.git(self.tools, 'commit', '--quiet', '-am', 'local')
        local = self.git(self.tools, 'rev-parse', 'HEAD')
        self.commit('two')
        self.assertIn('not an ancestor of origin/main', self.follow(1))
        self.assertEqual(self.git(self.tools, 'rev-parse', 'HEAD'), local)
        self.assertIn('not an ancestor of origin/main', self.status.read_text())

    def test_failed_fetch_is_posted_to_status_once_and_exits_nonzero(self):
        old = self.git(self.tools, 'rev-parse', 'HEAD')
        self.commit('two')
        self.git(self.tools, 'remote', 'set-url', 'origin', str(self.root / 'missing.git'))
        self.assertIn('git fetch of origin main failed', self.follow(1))
        self.assertEqual(self.git(self.tools, 'rev-parse', 'HEAD'), old)
        posted = self.status.read_text().splitlines()
        self.assertEqual(len(posted), 1, posted)
        self.assertIn(f'tools checkout {self.tools} no longer follows main: git fetch of origin main failed', posted[0])
        self.follow(1)
        self.assertEqual(self.status.read_text().splitlines(), posted)
        self.git(self.tools, 'remote', 'set-url', 'origin', str(self.origin))
        self.assertIn('moved', self.follow())
        self.assertFalse((self.store / 'follow-main.held').exists())

    def test_github_ssh_origin_is_fetched_over_https(self):
        url = subprocess.CompletedProcess([], 0, 'git@github.com:owner/repo.git\n', '')
        with patch.object(R, 'git', return_value=url) as git:
            R.fetch_main(self.tools)
        fetch = git.call_args_list[-1].args
        self.assertIn('https://github.com/owner/repo.git', fetch)
        self.assertIn('credential.helper=!gh auth git-credential', fetch)
        self.assertIn('+refs/heads/main:refs/remotes/origin/main', fetch)



class KillScanTests(unittest.TestCase):
    def test_patterns(self):
        unsafe = [PARENT_KILL, 'p' + 'kill -f qseq.sh', '/usr/bin/p' + 'kill x', 'kill' + 'all coqc',
                  PGREP_KILL, 'kill -9 `p' + 'grep coqc`', 'p' + 'grep -P "$' + '$"',
                  "subprocess.run(['p" + "kill', '-f', name])"]
        safe = ['kill "$pid"', 'kill -TERM $watcher', 'os.kill(pid, signal.SIGTERM)', '# ' + PARENT_KILL,
                '    # never ' + PGREP_KILL, 'p=$(p' + 'grep -f x)', 'skill_level=3']
        for line in unsafe:
            with self.subTest(line=line):
                self.assertEqual(len(kill_scan.scan_text(line, 'x')), 1)
        for line in safe:
            with self.subTest(line=line):
                self.assertEqual(kill_scan.scan_text(line, 'x'), [])

    def test_tree_failures_scan_only_tools_scripts(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / 'tools').mkdir()
            (root / 'tools' / 'watch.sh').write_text('sleep 1\n' + PARENT_KILL + '\n')
            (root / 'tools' / 'notes.txt').write_text(PARENT_KILL + '\n')
            (root / 'docs.sh').write_text(PARENT_KILL + '\n')
            failures = kill_scan.tree_failures(root, ['tools/watch.sh', 'tools/notes.txt', 'docs.sh', 'tools/gone.sh'])
        self.assertEqual(len(failures), 1)
        self.assertTrue(failures[0].startswith('tools/watch.sh:2: '), failures)


def status(line):
    """Spell `$` + `?` at run time, so this file passes its own scan."""
    return line.replace('$RC', '$' + '?')


FALSE_RC_SCRIPT = status('#!/usr/bin/env bash\ncoqc X.v\necho "$(date -u +%FT%TZ) RUN-DONE rc=$RC"\n')


class StatusScanTests(unittest.TestCase):
    def test_status_read_after_substitution(self):
        unsafe = map(status, ['echo "$(date -u +%FT%TZ) RUN-DONE rc=$RC"', 'echo "`date` rc=$RC"',
                              'printf "%s %s\\n" "$(date)" $RC', 'x=$(cmd) rc=$RC', 'a; echo "$(date) $RC" >> log'])
        safe = map(status, ['rc=$RC', 'echo "$(date -u +%FT%TZ) RUN-DONE rc=$rc"', 'x=$(cmd) || exit $RC',
                            'current=$(lock); s=$RC', 'echo "rc=$RC at $(date)"', 'echo $((1 + 2)) $RC',
                            "echo '$(date) $RC'", 'v=$(cmd; echo $RC)', '# echo "$(date) rc=$RC"',
                            'x=$(cmd)  # rc=$RC'])
        for line in unsafe:
            with self.subTest(line=line):
                findings = kill_scan.scan_text(line, 'x')
                self.assertEqual(len(findings), 1)
                self.assertIn('rc=$? on its own line', findings[0].message())
        for line in safe:
            with self.subTest(line=line):
                self.assertEqual(kill_scan.scan_text(line, 'x'), [])

    def test_tree_failures_report_false_exit_codes(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / 'tools').mkdir()
            (root / 'tools' / 'lane.sh').write_text(status('coqc X.v\necho "$(date) RUN-DONE rc=$RC"\n'))
            failures = kill_scan.tree_failures(root, ['tools/lane.sh'])
        self.assertEqual(len(failures), 1)
        self.assertTrue(failures[0].startswith('tools/lane.sh:2: '), failures)


GIB = 2 ** 30


class HeavyAdmissionTests(Fixture):
    def setUp(self):
        super().setUp()
        self.cgroup = self.root / 'cgroup' / 'user.slice' / f'user-{os.getuid()}.slice'
        self.cgroup.mkdir(parents=True)
        self.environment.update(ZESU_CGROUP_ROOT=str(self.root / 'cgroup'), ZESU_HEAVY_POLL_SECONDS='0.05')

    def slice(self, anon_gib, shmem_gib, pressure, file_gib=500):
        (self.cgroup / 'memory.stat').write_text(
            f'anon {anon_gib * GIB}\nfile {file_gib * GIB}\nshmem {shmem_gib * GIB}\nactive_file {file_gib * GIB}\n')
        (self.cgroup / 'memory.pressure').write_text(
            f'some avg10=0.00 avg60={pressure:.2f} avg300=0.00 total=1\nfull avg10=0.00 avg60=0.00 avg300=0.00 total=1\n')

    def test_page_cache_does_not_count(self):
        self.slice(130, 9, 4.99, file_gib=900)
        self.assertEqual(R.heavy_load(self.cgroup), (139 * GIB, 4.99))
        R.wait_heavy_admission('gate', self.cgroup, sleep=lambda _: self.fail('held'))

    def test_notices_at_most_once_a_minute_while_held(self):
        clock = [0.0]
        sleeps = []

        def sleep(_seconds):
            sleeps.append(clock[0])
            clock[0] += 15
            if len(sleeps) == 10:
                self.slice(10, 0, 0.0)
        self.slice(130, 10, 0.0)
        with patch('sys.stderr') as stderr:
            R.wait_heavy_admission('gate', self.cgroup, sleep=sleep, clock=lambda: clock[0])
        notices = [call.args[0] for call in stderr.write.call_args_list if call.args[0].startswith('notice:')]
        self.assertEqual(len(sleeps), 10)
        self.assertEqual(len(notices), 3, notices)
        self.assertIn('anon+shmem 140.0 GiB (limit 140)', notices[0])

    def test_bg_heavy_waits_for_memory_and_pressure_then_launches(self):
        self.slice(150, 0, 0.0)
        process = subprocess.Popen([BG, '--heavy', '--owner', 'tester', 'gate', '--', sys.executable, '-c',
                                    'print("ran", flush=True)'], cwd=self.root, env=self.environment,
                                   stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
        self.processes.append(process)
        time.sleep(1)
        self.slice(100, 39, 6.0)
        time.sleep(1)
        self.assertIsNone(process.poll())
        self.assertEqual(self.systemd_calls(), [])
        self.slice(100, 39, 1.0)
        stdout, stderr = process.communicate(timeout=EVENT_CEILING_SECONDS)
        self.assertEqual(process.returncode, 0, stderr)
        notices = [line for line in stderr.splitlines() if 'heavy launch gate waits' in line]
        self.assertEqual(len(notices), 1, stderr)
        self.assertTrue(notices[0].startswith('notice: '))
        self.assertTrue(stdout.strip().startswith('tester-gate-'))
        self.wait_for(lambda: 'ran' in (self.root / 'gate.log').read_text())

    def test_unreadable_slice_is_an_error(self):
        result = self.cli('launch', '--heavy', '--name', 'gate', '--', 'true')
        self.assertEqual(result.returncode, 2, result.stderr)
        self.assertEqual(self.systemd_calls(), [])


class StallReportTests(Fixture):
    NOW = 1_800_000_000.0

    def run_dir(self, run_id, branch, gates_age_minutes=None, marker='gates.out'):
        directory = self.root / 'runs' / run_id
        directory.mkdir(parents=True)
        (directory / 'ITEM.json').write_text(json.dumps({'branch': branch}))
        if gates_age_minutes is not None:
            (directory / marker).write_text('done\n')
            stamp = self.NOW - gates_age_minutes * 60
            os.utime(directory / marker, (stamp, stamp))
        # A disposable scheduler: the fixture's close() stops live rows, never this test process.
        scheduler = subprocess.Popen(['sleep', '60'])
        self.registry.register(run_id, 'bg', 'tester', R.identity(scheduler.pid), ['true'],
                               {'run_dir': str(directory)})
        scheduler.kill()
        scheduler.wait(timeout=EVENT_CEILING_SECONDS)

    def test_posts_each_stalled_branch_once(self):
        gates_at = R.datetime.datetime.fromtimestamp(self.NOW - 40 * 60, R.datetime.timezone.utc)
        later = (gates_at + R.datetime.timedelta(minutes=5)).isoformat().replace('+00:00', 'Z')
        earlier = (gates_at - R.datetime.timedelta(minutes=5)).isoformat().replace('+00:00', 'Z')
        self.run_dir('stalled', 'w/stalled', 40)
        self.run_dir('merged', 'w/merged', 40)
        self.run_dir('active', 'w/active', 40, marker='GATES-DONE')
        self.run_dir('quiet', 'w/quiet', 40, marker='GATES-DONE')
        self.run_dir('fresh', 'w/fresh', 10)
        self.run_dir('nogates', 'w/nogates')
        self.run_dir('old', 'w/rerun', 90)
        self.run_dir('new', 'w/rerun')
        prs = {'w/stalled': [], 'w/merged': [{'state': 'MERGED', 'updatedAt': earlier}],
               'w/active': [{'state': 'OPEN', 'updatedAt': later}],
               'w/quiet': [{'state': 'OPEN', 'updatedAt': earlier}, {'state': 'CLOSED', 'updatedAt': later}]}
        asked = []

        def lookup(branch):
            asked.append(branch)
            return prs[branch]
        status = self.root / 'STATUS.md'
        messages = R.stall_report(self.registry, status, prs=lookup, now=self.NOW)
        done = R.time.strftime('%Y-%m-%dT%H:%MZ', R.time.gmtime(self.NOW - 40 * 60))
        self.assertEqual(len(messages), 2, messages)
        self.assertIn(f'gates done at {done} for branch w/quiet; no PR/merge since (run quiet', messages[0])
        self.assertIn(f'gates done at {done} for branch w/stalled; no PR/merge since (run stalled', messages[1])
        self.assertEqual(status.read_text(), ''.join(message + '\n' for message in messages))
        self.assertEqual(sorted(asked), ['w/active', 'w/merged', 'w/quiet', 'w/stalled'])
        asked.clear()
        self.assertEqual(R.stall_report(self.registry, status, prs=lookup, now=self.NOW), [])
        self.assertEqual(sorted(asked), ['w/active', 'w/merged'])

    def test_failed_lookup_posts_nothing_and_retries(self):
        self.run_dir('stalled', 'w/stalled', 40)
        status = self.root / 'STATUS.md'

        def broken(_branch):
            raise ValueError('gh: not logged in')
        [message] = R.stall_report(self.registry, status, prs=broken, now=self.NOW)
        self.assertIn('PR lookup for w/stalled failed: gh: not logged in', message)
        self.assertFalse(status.exists())
        self.assertEqual(len(R.stall_report(self.registry, status, prs=lambda _: [], now=self.NOW)), 1)



if __name__ == '__main__':
    unittest.main()
