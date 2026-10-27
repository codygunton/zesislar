"""Exercise run replacement with real disposable process trees."""

import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import time
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parent))
import run_registry as R


class RunRegistryTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.registry = R.Registry(self.root / 'registry')
        self.children = []
        self.wrappers = []

    def tearDown(self):
        for row in self.registry.active():
            if row['scheduler']['pid'] != os.getpid():
                self.registry.stop(row['id'], grace=0.5)
        for process in self.children + self.wrappers:
            if process.poll() is None:
                process.kill()
            process.wait(timeout=5)

    def wait_for(self, predicate):
        deadline = time.monotonic() + 5
        while time.monotonic() < deadline:
            result = predicate()
            if result:
                return result
            time.sleep(0.02)
        self.fail('The disposable fixture did not reach its expected state.')

    def sleeper(self):
        process = subprocess.Popen([sys.executable, '-c', 'import time; time.sleep(60)'])
        self.children.append(process)
        self.wait_for(lambda: R.identity(process.pid))
        return process

    def command(self, *arguments):
        return [sys.executable, '-B', str(Path(R.__file__)),
                '--store', str(self.registry.directory), *arguments]

    def wrapper(self, run_id, code, *options):
        process = subprocess.Popen(self.command(
            'run', '--id', run_id, '--kind', 'fixture', '--owner', 'test',
            *options, '--', sys.executable, '-c', code),
            stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
        self.wrappers.append(process)
        return process

    def test_completed_run_records_command_and_exit_status(self):
        process = self.wrapper('complete', 'raise SystemExit(7)')
        self.assertEqual(process.wait(timeout=5), 7)
        row = self.registry.read()['runs']['complete']
        self.assertEqual(row['status'], 'failed')
        self.assertEqual(row['exit_code'], 7)
        self.assertTrue(row['all_actors_closed'])
        self.assertEqual(self.registry.active(), [])

    def test_duplicate_run_id_refuses_without_replacing_existing_identity(self):
        scheduler = self.sleeper()
        actor = R.identity(scheduler.pid)
        self.registry.register('same', 'fixture', 'test', actor, [])
        with self.assertRaisesRegex(ValueError, 'already exists'):
            self.registry.register('same', 'fixture', 'test', actor, [])
        self.assertEqual(self.registry.read()['runs']['same']['scheduler'], actor)

    def test_reused_pid_identity_never_receives_a_signal(self):
        actor = {**R.identity(os.getpid()), 'startticks': 0}
        with patch.object(R, 'open_pidfd') as opening:
            self.assertFalse(R.send_signal(actor, R.signal.SIGTERM))
            opening.assert_not_called()

    def test_libc_pidfd_route_closes_exact_actor_without_python_bindings(self):
        child = self.sleeper()
        actor = R.identity(child.pid)
        with patch.object(os, 'pidfd_open', None, create=True), \
                patch.object(R.signal, 'pidfd_send_signal', None, create=True):
            self.assertTrue(R.send_signal(actor, R.signal.SIGTERM))
            child.wait(timeout=5)
            self.assertFalse(R.send_signal(actor, R.signal.SIGTERM))

    def test_dead_scheduler_does_not_hide_a_live_registered_job(self):
        scheduler = self.sleeper()
        job = self.sleeper()
        self.registry.register('orphan', 'fixture', 'test', R.identity(scheduler.pid), [])
        self.registry.add_job('orphan', R.identity(job.pid))
        scheduler.terminate()
        scheduler.wait(timeout=5)
        self.assertEqual(len(self.registry.active()), 1)
        with self.assertRaisesRegex(ValueError, 'live jobs'):
            self.registry.release_claims('orphan')
        self.registry.stop('orphan', grace=0.5)
        self.assertFalse(R.live(R.identity(job.pid)) if R.identity(job.pid) else False)
        self.assertEqual(self.registry.active(), [])

    def test_supersession_closes_nested_jobs_and_releases_before_launch(self):
        old = self.wrapper('old',
            'import subprocess,sys,time; '
            'subprocess.Popen([sys.executable,"-c","import time;time.sleep(60)"]); '
            'time.sleep(60)')
        def ready():
            row = self.registry.read()['runs'].get('old')
            return row if row and len(row['jobs']) >= 2 else None
        previous = self.wait_for(ready)
        released = self.root / 'released'
        self.registry.add_claim('old', 'memory', [sys.executable, '-c',
            'from pathlib import Path;Path(sys.argv[1]).write_text("released")'
            .replace('from pathlib', 'import sys;from pathlib'), str(released)])
        new = self.wrapper('new',
            f'from pathlib import Path;assert Path({str(released)!r}).read_text()=="released"',
            '--supersedes', 'old')
        self.assertEqual(new.wait(timeout=10), 0)
        old.wait(timeout=5)
        for actor in [previous['scheduler']] + previous['jobs']:
            self.assertFalse(R.live(actor))
        row = self.registry.read()['runs']['old']
        self.assertEqual(row['status'], 'stopped')
        self.assertTrue(row['claims']['memory']['released'])

    def test_failed_claim_release_prevents_replacement(self):
        old = self.wrapper('old', 'import time;time.sleep(60)')
        self.wait_for(lambda: self.registry.read()['runs'].get('old'))
        self.registry.add_claim('old', 'memory', [sys.executable, '-c', 'raise SystemExit(4)'])
        marker = self.root / 'started'
        new = self.wrapper('new', f'from pathlib import Path;Path({str(marker)!r}).touch()',
                           '--supersedes', 'old')
        self.assertEqual(new.wait(timeout=10), 2)
        old.wait(timeout=5)
        self.assertFalse(marker.exists())
        self.assertNotIn('new', self.registry.read()['runs'])
        self.assertFalse(self.registry.read()['runs']['old']['claims']['memory']['released'])
        # Preserve the failed release record while allowing fixture cleanup.
        self.registry.claim_released('old', 'memory')

    def test_normal_claim_release_runs_once(self):
        scheduler = self.sleeper()
        self.registry.register('release', 'fixture', 'test', R.identity(scheduler.pid), [])
        output = self.root / 'count'
        self.registry.add_claim('release', 'memory', [sys.executable, '-c',
            'from pathlib import Path;import sys;p=Path(sys.argv[1]);'
            'p.write_text(p.read_text()+"x" if p.exists() else "x")', str(output)])
        scheduler.terminate()
        scheduler.wait(timeout=5)
        self.registry.release_claims('release')
        self.registry.release_claims('release')
        self.assertEqual(output.read_text(), 'x')

    def test_replacement_refuses_another_owner(self):
        child = self.sleeper()
        self.registry.register('old', 'fixture', 'other', R.identity(child.pid), [])
        new = self.wrapper('new', 'pass', '--supersedes', 'old')
        self.assertEqual(new.wait(timeout=5), 2)
        self.assertTrue(R.live(R.identity(child.pid)))

    def test_begin_and_register_detached_job_validate_startticks(self):
        child = self.sleeper()
        actor = R.identity(child.pid)
        result = subprocess.run(self.command('begin', '--id', 'external', '--kind', 'fixture',
            '--owner', 'test', '--pid', str(child.pid), '--startticks', str(actor['startticks'])),
            capture_output=True, text=True)
        self.assertEqual(result.returncode, 0, result.stderr)
        job = self.sleeper()
        wrong = subprocess.run(self.command('register-job', '--run-id', 'external',
            '--pid', str(job.pid), '--startticks', '0'), capture_output=True, text=True)
        self.assertEqual(wrong.returncode, 2)
        correct = subprocess.run(self.command('register-job', '--run-id', 'external',
            '--pid', str(job.pid), '--startticks', str(R.identity(job.pid)['startticks'])),
            capture_output=True, text=True)
        self.assertEqual(correct.returncode, 0, correct.stderr)
        self.assertIn(job.pid, [a['pid'] for a in self.registry.active()[0]['live_actors']])

    def test_list_active_json_excludes_fully_closed_runs(self):
        process = self.wrapper('complete', 'pass')
        self.assertEqual(process.wait(timeout=5), 0)
        output = subprocess.check_output(self.command('list', '--active', '--json'), text=True)
        self.assertEqual(json.loads(output), [])


if __name__ == '__main__':
    unittest.main()
