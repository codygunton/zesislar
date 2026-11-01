"""Exercise run replacement with real disposable process trees."""

import json
from types import SimpleNamespace
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import time
import unittest
from unittest.mock import MagicMock, patch

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

    def test_signal_during_locked_update_does_not_deadlock(self):
        code = '''
import os, signal, sys
from types import SimpleNamespace
from unittest.mock import patch
sys.path.insert(0, sys.argv[1])
import run_registry as R
registry = R.Registry(sys.argv[2])
original = registry.refresh
signalled = False
def refresh(run_id):
    global signalled
    if signalled:
        return original(run_id)
    signalled = True
    def operation(row):
        row['fixture_signal_during_update'] = True
        os.kill(os.getpid(), signal.SIGTERM)
    return registry.update(run_id, operation)
args = SimpleNamespace(id='interrupted', kind='fixture', owner='test', supersedes=[],
                       command=[sys.executable, '-c', 'import time;time.sleep(60)'])
with patch.object(registry, 'refresh', side_effect=refresh):
    raise SystemExit(R.run_command(registry, args))
'''
        result = subprocess.run([sys.executable, '-B', '-c', code,
            str(Path(R.__file__).parent), str(self.registry.directory)],
            capture_output=True, text=True, timeout=5)
        self.assertEqual(result.returncode, 143, result.stderr)
        row = self.registry.read_run('interrupted')
        self.assertTrue(row['fixture_signal_during_update'])
        self.assertTrue(row['all_actors_closed'])
        self.assertEqual(self.registry.active(), [])

    def registration_signal(self, checkpoint, source=None, directory=None):
        code = r"""
import os,signal,sys
from pathlib import Path
from types import SimpleNamespace
from unittest.mock import patch
sys.path.insert(0,sys.argv[1])
import run_registry as R
registry=R.Registry(sys.argv[2]);checkpoint=sys.argv[3]
method='register' if checkpoint=='before' else 'add_job'
original=getattr(registry,method)
def interrupted(*args,**kwargs):
    if checkpoint=='during':os.kill(os.getpid(),signal.SIGTERM)
    result=original(*args,**kwargs)
    if checkpoint=='before':os.kill(os.getpid(),signal.SIGTERM)
    return result
args=SimpleNamespace(id='registration',kind='fixture',owner='test',supersedes=[],
    command=[sys.executable,'-c','import time;time.sleep(60)'])
with patch.object(registry,method,side_effect=interrupted):
    raise SystemExit(R.run_command(registry,args))
"""
        result=subprocess.run([sys.executable,'-B','-c',code,
            str(source or Path(R.__file__).parent),str(directory or self.registry.directory),checkpoint],
            capture_output=True,text=True,timeout=5)
        self.assertEqual(result.returncode,143,result.stderr)
        row=R.Registry(directory or self.registry.directory).read()['runs']['registration']
        self.assertTrue(row['all_actors_closed'])
        self.assertTrue(all(not R.live(actor) for actor in row['jobs']))
        if checkpoint=='before':self.assertEqual(row['jobs'],[])

    def test_cancellation_before_child_launch_starts_no_child(self):
        self.registration_signal('before')

    def test_cancellation_during_child_registration_closes_exact_child(self):
        self.registration_signal('during')

    def test_harness_registry_cancellation_during_registration(self):
        # The harness retains the v1 protocol. Its cancellation must also work.
        self.registration_signal('during',Path(R.__file__).parent/'block/harness/runtime-tools',self.root/'harness-registry')

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

    def check_stop_lock_order(self, target):
        """Try to hold state.lock immediately before the selected stop signal."""
        command_read, command_write = os.pipe()
        response_read, response_write = os.pipe()
        descriptors = [command_read, command_write, response_read, response_write]
        holder_code = '''
import fcntl, os, sys
from pathlib import Path
lock_path, ready, command, response = sys.argv[1:]
command, response = int(command), int(response)
Path(ready).touch()
while os.read(command, 1):
    handle = open(lock_path, 'a')
    try:
        fcntl.flock(handle, fcntl.LOCK_EX | fcntl.LOCK_NB)
    except BlockingIOError:
        handle.close()
        os.write(response, b'blocked')
    else:
        os.write(response, b'held')
        # Retain the acquired lock until the fixture exits. An unsafe stop
        # freezes this holder and then deadlocks at its next refresh.
        while True:
            os.read(command, 1)
'''
        holder = None
        stopper = None
        scheduler = None
        try:
            ready = self.root / 'holder-ready'
            holder = subprocess.Popen([sys.executable, '-c', holder_code,
                str(self.registry.directory / 'state.lock'), str(ready),
                str(command_read), str(response_write)],
                pass_fds=(command_read, response_write))
            self.children.append(holder)
            self.wait_for(ready.exists)
            scheduler = holder if target == 'scheduler' else self.sleeper()
            self.registry.register('locking', 'fixture', 'test', R.identity(scheduler.pid), [])
            if target == 'child':
                self.registry.add_job('locking', R.identity(holder.pid))
            unrelated = self.sleeper()
            receipt = self.root / 'lock-at-stop'
            release = self.root / 'released'
            self.registry.add_claim('locking', 'memory', [sys.executable, '-c',
                'import fcntl,sys;from pathlib import Path;'
                'h=open(sys.argv[1],"a");fcntl.flock(h,fcntl.LOCK_EX|fcntl.LOCK_NB);'
                'p=Path(sys.argv[2]);p.write_text(p.read_text()+"x" if p.exists() else "x")',
                str(self.registry.directory / 'state.lock'), str(release)])
            stopper_code = '''
import os, sys
from pathlib import Path
sys.path.insert(0, sys.argv[1])
import run_registry as R
store, target, command, response, receipt = sys.argv[2:]
target, command, response = int(target), int(command), int(response)
original = R.send_signal
probed = False
def probe(actor, value):
    global probed
    if not probed and actor['pid'] == target and value == R.signal.SIGSTOP:
        probed = True
        os.write(command, b'p')
        Path(receipt).write_text(os.read(response, 16).decode())
    return original(actor, value)
R.send_signal = probe
R.Registry(store).stop('locking', grace=0.5)
'''
            stopper = subprocess.Popen([sys.executable, '-B', '-c', stopper_code,
                str(Path(R.__file__).parent), str(self.registry.directory), str(holder.pid),
                str(command_write), str(response_read), str(receipt)],
                pass_fds=(command_write, response_read))
            self.wrappers.append(stopper)
            self.assertEqual(stopper.wait(timeout=5), 0)
            self.assertEqual(receipt.read_text(), 'blocked')
            self.assertTrue(R.live(R.identity(unrelated.pid)))
            row = self.registry.read()['runs']['locking']
            self.assertTrue(row['all_actors_closed'])
            self.assertTrue(row['claims']['memory']['released'])
            self.assertEqual(release.read_text(), 'x')
            self.registry.release_claims('locking')
            self.assertEqual(release.read_text(), 'x')
            self.assertFalse(R.live(row['scheduler']))
            self.assertTrue(all(not R.live(actor) for actor in row['jobs']))
        finally:
            # A regression can freeze the fixture with its lock held. Kill
            # only these disposable identities before registry-based cleanup.
            for process in (stopper, holder, scheduler):
                if process is not None and process.poll() is None:
                    process.kill()
                if process is not None:
                    process.wait(timeout=5)
            for descriptor in descriptors:
                os.close(descriptor)

    def test_stop_does_not_freeze_a_scheduler_holding_state_lock(self):
        self.check_stop_lock_order('scheduler')

    def test_stop_does_not_freeze_a_child_holding_state_lock(self):
        self.check_stop_lock_order('child')

    def test_freeze_failure_resumes_every_stopped_actor(self):
        scheduler, child = self.sleeper(), self.sleeper()
        self.registry.register('failure', 'fixture', 'test', R.identity(scheduler.pid), [])
        self.registry.add_job('failure', R.identity(child.pid))
        with patch.object(self.registry, 'save_row', side_effect=OSError('fixture write failure')):
            with self.assertRaisesRegex(OSError, 'fixture write failure'):
                self.registry.stop('failure', grace=0.5)
        self.wait_for(lambda: all(R.identity(p.pid)['state'] not in ('T', 't')
                                  for p in (scheduler, child)))
        self.assertTrue(all(R.live(R.identity(p.pid)) for p in (scheduler, child)))

    def test_unstopped_actor_refuses_within_grace_and_keeps_its_claim(self):
        scheduler = self.sleeper()
        actor = R.identity(scheduler.pid)
        self.registry.register('unstopped', 'fixture', 'test', actor, [])
        self.registry.add_claim('unstopped', 'memory', [sys.executable, '-c', 'pass'])
        actual_identity = R.identity
        actual_signal = R.send_signal
        sent = []

        def unstopped(pid, *args):
            current = actual_identity(pid, *args)
            if current and pid == actor['pid']:
                return dict(current, state='S')
            return current

        def record_signal(target, value):
            sent.append(value)
            return actual_signal(target, value)

        with patch.object(R, 'identity', side_effect=unstopped), \
                patch.object(R, 'send_signal', side_effect=record_signal):
            with self.assertRaisesRegex(ValueError, 'grace interval'):
                self.registry.stop('unstopped', grace=0.03)
        self.wait_for(lambda: actual_identity(scheduler.pid)['state'] not in ('T', 't'))
        self.assertIn(R.signal.SIGCONT, sent)
        self.assertNotIn(R.signal.SIGTERM, sent)
        self.assertNotIn(R.signal.SIGKILL, sent)
        row = self.registry.read()['runs']['unstopped']
        self.assertEqual(row['status'], 'stop_failed')
        self.assertFalse(row['all_actors_closed'])
        self.assertEqual([R.actor_key(a) for a in row['stop_pending']], [R.actor_key(actor)])
        self.assertFalse(row['claims']['memory']['released'])
        self.assertTrue(R.live(actor))

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


class PerRunRegistryTests(RunRegistryTests):
    """Run the same actor, stop, release, and supersession controls in v2."""

    def setUp(self):
        super().setUp()
        self.registry.migrate()


class RegistryScalingTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.registry = R.Registry(Path(self.temp.name) / 'registry')

    def seed(self, *names):
        rows = {name: {'id': name, 'kind': 'fixture', 'owner': 'test',
                      'scheduler': {'pid': 0, 'startticks': 0, 'ppid': 0, 'state': 'X'},
                      'jobs': [], 'claims': {}, 'status': 'completed'} for name in names}
        self.registry.write({'schema': 'zesu.run-registry.v1', 'runs': rows})
        return rows

    def test_default_store_remains_v1(self):
        self.seed('old')
        self.assertEqual(self.registry.header()['schema'], 'zesu.run-registry.v1')
        self.assertFalse((self.registry.directory / 'runs.d').exists())

    def test_migration_preserves_rows_and_original_snapshot(self):
        rows = self.seed('old', '../separated/id')
        rows['old']['claims']['memory'] = {'released': True, 'release_command': ['true']}
        self.registry.write({'schema': 'zesu.run-registry.v1', 'runs': rows})
        self.registry.migrate()
        header = self.registry.header()
        self.assertEqual(self.registry.read()['runs'], rows)
        self.assertEqual(self.registry.read_file(
            self.registry.directory / header['legacy_snapshot'])['runs'], rows)
        self.assertEqual(self.registry.row_path('../separated/id').parent,
                         self.registry.directory / 'runs.d')
        # The former v1 reader rejects the protocol marker before writing.
        self.assertNotEqual(json.loads(self.registry.path.read_text())['schema'],
                            'zesu.run-registry.v1')
        with self.assertRaisesRegex(ValueError, 'bulk write'):
            self.registry.write({'schema': 'zesu.run-registry.v1', 'runs': {}})

    def test_migration_refuses_live_scheduler_or_detached_job(self):
        for location in ('scheduler', 'jobs'):
            with self.subTest(location=location):
                rows = self.seed('old')
                actor = R.identity(os.getpid())
                rows['old'][location] = actor if location == 'scheduler' else [actor]
                self.registry.write({'schema': 'zesu.run-registry.v1', 'runs': rows})
                with self.assertRaisesRegex(ValueError, 'closed actors'):
                    self.registry.migrate()
                self.assertEqual(self.registry.header()['schema'], 'zesu.run-registry.v1')

    def test_migration_refuses_unreleased_claim(self):
        rows = self.seed('old')
        rows['old']['claims']['memory'] = {'released': False, 'release_command': ['true']}
        self.registry.write({'schema': 'zesu.run-registry.v1', 'runs': rows})
        with self.assertRaisesRegex(ValueError, 'released claims'):
            self.registry.migrate()

    def test_interrupted_migration_retains_v1_authority(self):
        rows = self.seed('old')
        original = self.registry.path.read_bytes()
        with patch.object(self.registry, 'atomic_write', side_effect=OSError('fixture failure')):
            with self.assertRaisesRegex(OSError, 'fixture failure'):
                self.registry.migrate()
        self.assertEqual(self.registry.path.read_bytes(), original)
        self.assertEqual(self.registry.read()['runs'], rows)

    def test_unpublished_per_run_directory_is_never_adopted(self):
        self.seed('old')
        (self.registry.directory / 'runs.d').mkdir()
        with self.assertRaisesRegex(ValueError, 'blocks migration'):
            self.registry.migrate()
        self.assertEqual(self.registry.header()['schema'], 'zesu.run-registry.v1')

    def test_run_directory_is_durable_before_marker_publication(self):
        self.seed('old')
        events = []
        rename, sync, write = R.os.rename, R.Registry.sync_directory, self.registry.atomic_write
        def record_rename(source, target):
            rename(source, target)
            events.append('rename')
        def record_sync(path):
            sync(path)
            if path == self.registry.directory:
                events.append('parent_sync')
        def record_write(path, value):
            if path == self.registry.path:
                self.assertEqual(events[-2:], ['rename', 'parent_sync'])
                events.append('marker')
            write(path, value)
        with patch.object(R.os, 'rename', side_effect=record_rename), \
                patch.object(R.Registry, 'sync_directory', side_effect=record_sync), \
                patch.object(self.registry, 'atomic_write', side_effect=record_write):
            self.registry.migrate()
        self.assertIn('marker', events)

    def test_v2_missing_run_directory_refuses_history_and_updates(self):
        self.seed('old')
        self.registry.migrate()
        directory = self.registry.directory / 'runs.d'
        directory.rename(self.registry.directory / 'retained-runs.d')
        for operation in (self.registry.read,
                          lambda: self.registry.read_run('old'),
                          lambda: self.registry.update('old', lambda row: None)):
            with self.assertRaisesRegex(ValueError, 'directory is missing'):
                operation()

    def test_per_run_update_does_not_read_or_replace_historical_rows(self):
        self.seed('old', 'active')
        self.registry.migrate()
        old = self.registry.row_path('old')
        before = (old.stat().st_ino, old.read_bytes())
        reader = self.registry.read_file
        def read_without_history(path):
            self.assertNotEqual(path, old)
            return reader(path)
        with patch.object(self.registry, 'read_file', side_effect=read_without_history):
            self.registry.update('active', lambda row: row.update(status='failed'))
        self.assertEqual((old.stat().st_ino, old.read_bytes()), before)
        self.assertEqual(self.registry.read_run('active')['status'], 'failed')

    def test_noop_update_and_state_only_refresh_do_not_write(self):
        self.seed('old')
        actor = {'pid': 123, 'startticks': 45, 'ppid': 67, 'state': 'R'}
        self.registry.update('old', lambda row: row['jobs'].append(actor))
        with patch.object(self.registry, 'save_row') as saving, \
                patch.object(R, 'descendants', return_value=[dict(actor, state='S')]):
            self.registry.refresh('old')
            self.registry.update('old', lambda row: None)
            saving.assert_not_called()
        with patch.object(R, 'descendants', return_value=[dict(actor, startticks=46)]):
            row = self.registry.refresh('old')
        self.assertEqual([a['startticks'] for a in row['jobs']], [45, 46])

    def test_per_run_record_id_mismatch_refuses(self):
        self.seed('old')
        self.registry.migrate()
        path = self.registry.row_path('old')
        row = self.registry.read_run('old')
        row['id'] = 'other'
        self.registry.atomic_write(path, row)
        with self.assertRaisesRegex(ValueError, 'does not match'):
            self.registry.read_run('old')
        with self.assertRaisesRegex(ValueError, 'invalid ID'):
            self.registry.read()

    def test_routine_refresh_is_throttled_and_final_refresh_is_immediate(self):
        registry = MagicMock()
        registry.contains.return_value = False
        registry.refresh.return_value = {'status': 'running', 'jobs': []}
        process = MagicMock(pid=999999999)
        process.poll.side_effect = [None] * 71 + [0]
        process.wait.return_value = 0
        clock, samples = [0.0], []
        registry.refresh.side_effect = lambda run_id: (
            samples.append(clock[0]) or {'status': 'running', 'jobs': []})
        args = SimpleNamespace(command=['true'], owner='test', id='fixture',
                               kind='fixture', supersedes=[])
        with patch.object(R.subprocess, 'Popen', return_value=process), \
                patch.object(R.time, 'monotonic', side_effect=lambda: clock[0]), \
                patch.object(R.time, 'sleep', side_effect=lambda t: clock.__setitem__(0, clock[0] + t)):
            self.assertEqual(R.run_command(registry, args), 0)
        self.assertEqual(len(samples), 4)
        self.assertGreaterEqual(samples[1] - samples[0], 3)
        self.assertGreaterEqual(samples[2] - samples[1], 3)
        self.assertAlmostEqual(samples[-1], 7.1)
        self.assertLess(samples[-1] - samples[-2], 3)


if __name__ == '__main__':
    unittest.main()
