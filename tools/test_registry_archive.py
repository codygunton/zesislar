"""Archive closed lifecycle records without changing a live registry."""

import json
import importlib.util
import os
import subprocess
from pathlib import Path
import sys
import tempfile
import threading
import time
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parent))
import run_registry as R


DAY_NS = 24 * 60 * 60 * 1_000_000_000


class RegistryArchiveTests(unittest.TestCase):
    per_run = False

    def setUp(self):
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)
        self.registry = R.Registry(self.root / 'registry')
        if self.per_run:
            self.registry.migrate()
        self.now_ns = time.time_ns()
        self.dead = {'pid': 2_000_000_000, 'startticks': 1, 'ppid': 1, 'state': 'Z'}

    def closed(self, run_id, age_ns=DAY_NS + 1):
        return {'id': run_id, 'kind': 'fixture', 'owner': 'test',
                'scheduler': self.dead.copy(), 'jobs': [], 'claims': {},
                'command': ['fixture'], 'registered_ns': self.now_ns - 2 * DAY_NS,
                'status': 'completed', 'closed_ns': self.now_ns - age_ns,
                'all_actors_closed': True, 'exit_code': 0}

    def seed(self, *rows):
        if self.per_run:
            for row in rows:
                self.registry.atomic_write(self.registry.row_path(row['id']), row)
        else:
            self.registry.write({'schema': 'zesu.run-registry.v1',
                                 'runs': {row['id']: row for row in rows}})

    def test_old_closed_history_remains_readable_and_id_stays_reserved(self):
        row = self.closed('closed')
        self.seed(row)
        self.registry.compact(now_ns=self.now_ns)
        self.assertEqual(self.registry.read_run('closed'), row)
        self.assertEqual(self.registry.read()['runs']['closed'], row)
        self.assertTrue(self.registry.contains('closed'))
        self.assertEqual(self.registry.active(), [])
        with self.assertRaisesRegex(ValueError, 'already exists'):
            self.registry.register('closed', 'fixture', 'test', R.identity(os.getpid()), [])

    def test_exact_day_and_recent_rows_stay_in_active_store(self):
        rows = [self.closed('exact', DAY_NS), self.closed('recent', DAY_NS - 1)]
        self.seed(*rows)
        before = self.registry.path.read_bytes()
        self.registry.compact(now_ns=self.now_ns)
        self.assertEqual(self.registry.path.read_bytes(), before)
        for row in rows:
            self.assertEqual(self.registry.read_run(row['id']), row)

    def test_live_actor_pending_claim_and_incomplete_closure_are_not_archived(self):
        rows = [self.closed(name) for name in ('live-owner', 'live-job', 'claim', 'incomplete')]
        rows[0]['scheduler'] = R.identity(os.getpid())
        rows[1]['jobs'] = [R.identity(os.getpid())]
        rows[2]['claims'] = {'memory': {'released': False, 'release_command': ['fixture']}}
        rows[3]['all_actors_closed'] = False
        self.seed(*rows)
        before = self.registry.path.read_bytes()
        self.registry.compact(now_ns=self.now_ns)
        self.assertEqual(self.registry.path.read_bytes(), before)

    def test_missing_close_time_does_not_qualify_for_retention_cutoff(self):
        row = self.closed('unknown-age')
        del row['closed_ns']
        self.seed(row)
        before = self.registry.path.read_bytes()
        self.registry.compact(now_ns=self.now_ns)
        self.assertEqual(self.registry.path.read_bytes(), before)
        self.assertEqual(self.registry.read_run(row['id']), row)

    def test_cli_history_reads_archived_and_recent_rows(self):
        rows = [self.closed('archived'), self.closed('recent', 1)]
        self.seed(*rows)
        self.registry.compact(now_ns=self.now_ns)
        result = subprocess.run([sys.executable, '-B', R.__file__, '--store',
            str(self.registry.directory), 'list', '--json'],
            capture_output=True, text=True, timeout=5)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual({row['id']: row for row in json.loads(result.stdout)},
                         {row['id']: row for row in rows})

    def test_history_preserves_non_path_run_ids(self):
        rows = [self.closed('../outside'), self.closed('nested/id'), self.closed('unicode-λ')]
        self.seed(*rows)
        self.registry.compact(now_ns=self.now_ns)
        for row in rows:
            self.assertEqual(self.registry.read_run(row['id']), row)
            self.assertTrue(self.registry.contains(row['id']))
        self.assertFalse((self.root / 'outside').exists())

    def test_repeated_compaction_preserves_history_bytes(self):
        row = self.closed('closed')
        self.seed(row)
        self.registry.compact(now_ns=self.now_ns)
        files = {str(p.relative_to(self.registry.directory)): p.read_bytes()
                 for p in self.registry.directory.rglob('*.json')}
        self.registry.compact(now_ns=self.now_ns)
        for name, raw in files.items():
            self.assertEqual((self.registry.directory / name).read_bytes(), raw)
        self.assertEqual(self.registry.read_run('closed'), row)

    def test_archived_mutations_refuse_without_running_callbacks(self):
        row = self.closed('closed')
        self.seed(row)
        self.registry.compact(now_ns=self.now_ns)
        path = self.registry.archive_path('closed')
        before = (path.stat().st_ino, path.read_bytes())
        called = []
        for operation in (lambda: self.registry.update('closed', lambda value: called.append(value)),
                          lambda: self.registry.stop('closed')):
            with self.assertRaisesRegex(ValueError, 'immutable'):
                operation()
        self.assertEqual(called, [])
        self.assertEqual((path.stat().st_ino, path.read_bytes()), before)

    def test_new_schema_reserves_history_without_scanning_archive_for_active_work(self):
        self.seed(self.closed('closed'))
        self.registry.compact(now_ns=self.now_ns)
        self.assertEqual(self.registry.header()['schema'], 'zesu.run-registry.v3')
        reader = self.registry.read_file
        def no_history(path):
            if path.exists():
                self.assertNotEqual(path.parent, self.registry.directory / 'archive.d')
            return reader(path)
        with patch.object(self.registry, 'read_file', side_effect=no_history):
            self.registry.register('new', 'fixture', 'test', R.identity(os.getpid()), [])
            self.assertEqual([r['id'] for r in self.registry.active()], ['new'])
            self.registry.update('new', lambda value: value.update(command=['updated']))
        self.assertEqual(self.registry.read_run('closed')['id'], 'closed')

    def test_format_switch_refuses_another_live_actor(self):
        old = self.closed('closed')
        active = self.closed('live', age_ns=1)
        active['scheduler'] = R.identity(os.getpid())
        self.seed(old, active)
        before = self.registry.path.read_bytes()
        with self.assertRaisesRegex(ValueError, 'closed actors'):
            self.registry.compact(now_ns=self.now_ns)
        self.assertEqual(self.registry.path.read_bytes(), before)

    def test_marker_publication_crash_keeps_history_and_retry_removes_duplicate(self):
        row = self.closed('closed')
        self.seed(row)
        original = Path.unlink
        target = self.registry.row_path('closed')
        def interrupted(path, *args, **kwargs):
            if path == target:
                raise OSError('fixture after marker publication')
            return original(path, *args, **kwargs)
        with patch.object(Path, 'unlink', new=interrupted):
            with self.assertRaisesRegex(OSError, 'after marker'):
                self.registry.compact(now_ns=self.now_ns)
        reopened = R.Registry(self.registry.directory)
        self.assertEqual(reopened.header()['schema'], 'zesu.run-registry.v3')
        self.assertEqual(reopened.read()['runs'], {'closed': row})
        self.assertEqual(reopened.read_run('closed'), row)
        reopened.compact(now_ns=self.now_ns)
        self.assertFalse(target.exists())
        self.assertEqual(reopened.read_run('closed'), row)

    def test_missing_archive_directory_refuses_history(self):
        self.seed(self.closed('closed'))
        self.registry.compact(now_ns=self.now_ns)
        archive = self.registry.directory / 'archive.d'
        archive.rename(self.registry.directory / 'retained-archive.d')
        for operation in (self.registry.read, lambda: self.registry.read_run('closed')):
            with self.assertRaisesRegex(ValueError, 'archive directory is missing'):
                operation()

    def test_existing_conflicting_archive_never_changes_the_authoritative_store(self):
        row = self.closed('closed')
        self.seed(row)
        archive = self.registry.directory / 'archive.d'
        archive.mkdir()
        conflicting = dict(row, exit_code=99)
        self.registry.atomic_write(self.registry.archive_path('closed'), conflicting)
        before = self.registry.path.read_bytes()
        with self.assertRaisesRegex(ValueError, 'unpublished archive'):
            self.registry.compact(now_ns=self.now_ns)
        self.assertEqual(self.registry.path.read_bytes(), before)
        self.assertEqual(self.registry.read_run('closed'), row)

    def test_cli_requires_an_explicit_store_before_compaction(self):
        self.seed(self.closed('closed'))
        result = subprocess.run([sys.executable, '-B', R.__file__, 'compact'],
            env=dict(os.environ, ZESU_RUN_REGISTRY=str(self.registry.directory)),
            capture_output=True, text=True, timeout=5)
        self.assertEqual(result.returncode, 2)
        self.assertIn('explicit --store', result.stderr)
        self.assertFalse((self.registry.directory / 'archive.d').exists())


    def test_failed_active_write_keeps_history_and_can_retry(self):
        row = self.closed('closed')
        self.seed(row)
        original = self.registry.atomic_write
        def interrupted(path, value):
            if path == self.registry.path or (self.per_run and path == self.registry.row_path('closed')):
                raise OSError('fixture publication failure')
            return original(path, value)
        with patch.object(self.registry, 'atomic_write', side_effect=interrupted):
            with self.assertRaisesRegex(OSError, 'fixture publication failure'):
                self.registry.compact(now_ns=self.now_ns)
        reopened = R.Registry(self.registry.directory)
        self.assertEqual(reopened.read_run('closed'), row)
        self.assertTrue(reopened.contains('closed'))
        reopened.compact(now_ns=self.now_ns)
        self.assertEqual(reopened.read()['runs']['closed'], row)

    def test_compaction_cannot_allow_concurrent_id_reuse(self):
        row = self.closed('closed')
        self.seed(row)
        barrier = threading.Barrier(2)
        failures = []
        def compact():
            try:
                barrier.wait(timeout=5)
                self.registry.compact(now_ns=self.now_ns)
            except BaseException as error:
                failures.append(error)
        worker = threading.Thread(target=compact)
        worker.start()
        try:
            barrier.wait(timeout=5)
            with self.assertRaisesRegex(ValueError, 'already exists'):
                self.registry.register('closed', 'fixture', 'test', R.identity(os.getpid()), [])
        finally:
            worker.join(timeout=10)
        self.assertFalse(worker.is_alive())
        self.assertEqual(failures, [])
        self.assertEqual(self.registry.read_run('closed'), row)


class PerRunRegistryArchiveTests(RegistryArchiveTests):
    per_run = True


class RuntimeRegistryArchiveTests(RegistryArchiveTests):
    def setUp(self):
        path = Path(__file__).resolve().parent / 'block/harness/runtime-tools/run_registry.py'
        spec = importlib.util.spec_from_file_location('archive_runtime_registry', path)
        module = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(module)
        override = patch(__name__ + '.R', module)
        override.start()
        self.addCleanup(override.stop)
        super().setUp()


class RuntimePerRunRegistryArchiveTests(RuntimeRegistryArchiveTests):
    per_run = True


if __name__ == '__main__':
    unittest.main()
