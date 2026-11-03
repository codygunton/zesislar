"""Keep slow actor discovery outside the registry transaction."""

import importlib.util
from pathlib import Path
import subprocess
import sys
import tempfile
import threading
from types import SimpleNamespace
import unittest
from unittest.mock import MagicMock, patch

sys.path.insert(0, str(Path(__file__).resolve().parent))
import run_registry


class RegistryRefreshTests(unittest.TestCase):
    module = run_registry
    per_run = False

    def setUp(self):
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)
        self.registry = self.module.Registry(self.root / 'registry')
        if self.per_run:
            self.registry.migrate()
        self.scheduler = self.sleeper()
        self.registry.register('fixture', 'fixture', 'test',
                               self.module.identity(self.scheduler.pid), [])

    def sleeper(self):
        process = subprocess.Popen([sys.executable, '-c', 'import time;time.sleep(60)'])
        def close():
            if process.poll() is None:
                process.kill()
            process.wait(timeout=5)
        self.addCleanup(close)
        return process

    def concurrent_refresh(self, mutation):
        entered, resume, completed = (threading.Event() for _ in range(3))
        failures, results, discoveries = [], [], []
        actual = self.module.descendants

        def discover(actors):
            if threading.current_thread() is refresher:
                discoveries.append(actors)
                if len(discoveries) == 1:
                    entered.set()
                    if not resume.wait(5):
                        raise TimeoutError('The fixture did not release discovery.')
            return actual(actors)

        def refresh():
            try:
                results.append(self.registry.refresh('fixture'))
            except BaseException as error:
                failures.append(error)

        def update():
            try:
                mutation()
            except BaseException as error:
                failures.append(error)
            finally:
                completed.set()

        refresher = threading.Thread(target=refresh)
        updater = threading.Thread(target=update)
        with patch.object(self.module, 'descendants', side_effect=discover):
            refresher.start()
            try:
                self.assertTrue(entered.wait(5), 'Discovery did not start.')
                updater.start()
                self.assertTrue(completed.wait(2),
                                'Slow discovery retained the registry lock.')
            finally:
                resume.set()
                refresher.join(timeout=10)
                if updater.ident is not None:
                    updater.join(timeout=10)
        self.assertFalse(refresher.is_alive())
        self.assertFalse(updater.is_alive())
        self.assertEqual(failures, [])
        return results[0], discoveries

    def test_concurrent_job_and_claim_updates_survive_discovery(self):
        child = self.sleeper()
        other = self.sleeper()
        self.registry.register('other', 'fixture', 'test',
                               self.module.identity(other.pid), [])
        command = [sys.executable, '-c', 'pass']

        def mutation():
            self.registry.add_job('fixture', self.module.identity(child.pid))
            self.registry.add_claim('fixture', 'memory', command)
            self.registry.add_claim('other', 'other-memory', command)

        row, discoveries = self.concurrent_refresh(mutation)
        self.assertEqual(len(discoveries), 2)
        self.assertIn(child.pid, [a['pid'] for a in row['jobs']])
        self.assertEqual(row['claims']['memory'],
                         {'release_command': command, 'released': False})
        self.assertIn('other-memory', self.registry.read()['runs']['other']['claims'])
        self.assertEqual(self.registry.read()['runs']['fixture'], row)

    def test_concurrent_stop_and_claim_release_survive_discovery(self):
        marker = self.root / 'released'
        self.registry.add_claim('fixture', 'memory', [sys.executable, '-c',
            'from pathlib import Path;import sys;Path(sys.argv[1]).write_text("released")',
            str(marker)])
        row, discoveries = self.concurrent_refresh(
            lambda: self.registry.stop('fixture', grace=0.5))
        self.assertEqual(len(discoveries), 2)
        self.assertEqual(row['status'], 'stopped')
        self.assertTrue(row['all_actors_closed'])
        self.assertTrue(row['claims']['memory']['released'])
        self.assertEqual(marker.read_text(), 'released')
        self.assertFalse(self.module.live(self.module.identity(self.scheduler.pid))
                         if self.module.identity(self.scheduler.pid) else False)


class PerRunRegistryRefreshTests(RegistryRefreshTests):
    per_run = True


spec = importlib.util.spec_from_file_location('staged_refresh_registry',
    Path(__file__).parent / 'block/harness/runtime-tools/run_registry.py')
staged_registry = importlib.util.module_from_spec(spec)
spec.loader.exec_module(staged_registry)


class StagedRegistryRefreshTests(RegistryRefreshTests):
    module = staged_registry


class StagedRunCommandRefreshTests(unittest.TestCase):
    def test_routine_refresh_is_throttled_and_final_refresh_is_immediate(self):
        registry = MagicMock()
        registry.read.return_value = {'runs': {}}
        process = MagicMock(pid=999999999)
        process.poll.side_effect = [None] * 71 + [0]
        process.wait.return_value = 0
        clock, samples = [0.0], []
        registry.refresh.side_effect = lambda run_id: (
            samples.append(clock[0]) or {'status': 'running', 'jobs': []})
        args = SimpleNamespace(command=['true'], owner='test', id='fixture',
                               kind='fixture', supersedes=[])
        module = staged_registry
        with patch.object(module.subprocess, 'Popen', return_value=process), \
                patch.object(module.time, 'monotonic', side_effect=lambda: clock[0]), \
                patch.object(module.time, 'sleep', side_effect=lambda t: clock.__setitem__(0, clock[0] + t)):
            self.assertEqual(module.run_command(registry, args), 0)
        # The 0.1 second exit poll refreshes the registry only every 5 seconds.
        self.assertEqual(module.REFRESH_SECONDS, 5.0)
        self.assertEqual(len(samples), 3)
        self.assertGreaterEqual(samples[1] - samples[0], 5)
        self.assertAlmostEqual(samples[-1], 7.1)
        self.assertLess(samples[-1] - samples[-2], 5)


if __name__ == '__main__':
    unittest.main()
