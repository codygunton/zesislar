"""Launch long jobs outside the caller's tree, refuse unsafe kills, and ledger signal deaths."""

import json
import os
from pathlib import Path
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
        self.environment.pop('ZESU_RUN_ID', None)
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
            env=self.environment, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
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
                          'import os; print(os.environ.get("ZESU_RUN_ID"), os.environ.get("ZESU_BG_RUN_ID"))')
        self.assertEqual(result.returncode, 0, result.stderr)
        run_id = result.stdout.strip()
        self.wait_for(lambda: self.registry.read_run(run_id)['status'] == 'completed')
        self.assertEqual((self.root / 'env.log').read_text().split(), ['None', run_id])

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
        self.assertIn('run posted (owner test, kind fixture, unit none) ended by SIGKILL', message)
        self.assertIn('cause: unknown', message)
        self.assertEqual(status.read_text(), message + '\n')
        self.assertEqual(R.watchdog(self.registry, status), [])
        result = self.cli('watchdog', '--status', str(status))
        self.assertEqual((result.returncode, result.stdout), (0, ''), result.stderr)


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


if __name__ == '__main__':
    unittest.main()
