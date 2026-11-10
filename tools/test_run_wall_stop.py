"""Check that a wall-time stop finds and stops the run that holds a process."""

from pathlib import Path
import subprocess
import sys
import tempfile
import time
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parent))
import run_registry as R
import run_wall_stop as W

TOOLS = Path(__file__).resolve().parent
CEILING = 30.0

# A run command that starts one nested process and records its PID, as a
# guard batch starts a scope. With an argument it then stops its own run.
INSIDE = r'''
import os, pathlib, subprocess, sys
sys.path.insert(0, sys.argv[1])
import run_registry as R, run_wall_stop as W
out = pathlib.Path(sys.argv[2])
child = subprocess.Popen([sys.executable, '-c', 'import time; time.sleep(60)'])
(out / 'nested.pid').write_text(str(child.pid))
registry = R.Registry(pathlib.Path(os.environ['ZESU_RUN_REGISTRY']))
if sys.argv[3] == 'helper':
    run_id, how = W.stop_containing(child.pid, registry)
    (out / 'how').write_text(how)
elif sys.argv[3] == 'direct':
    try:
        registry.stop(os.environ['ZESU_RUN_ID'])
    except ValueError as error:
        (out / 'refused').write_text(str(error))
child.wait()
'''


class RunWallStopTests(unittest.TestCase):
    def setUp(self):
        temp = tempfile.TemporaryDirectory()
        self.addCleanup(temp.cleanup)
        self.root = Path(temp.name)
        self.registry = R.Registry(self.root / 'registry')
        self.processes = []
        self.addCleanup(self.close)

    def close(self):
        for row in self.registry.read()['runs'].values():
            for actor in [row['scheduler']] + row['jobs']:
                R.send_signal(actor, R.signal.SIGKILL)
        for process in self.processes:
            if process.poll() is None:
                process.kill()
            process.wait()

    def wait_for(self, predicate):
        deadline = time.monotonic() + CEILING
        while time.monotonic() < deadline:
            result = predicate()
            if result:
                return result
            time.sleep(0.05)
        self.fail('The fixture did not reach its expected state.')

    def start(self, run_id, mode='none'):
        process = subprocess.Popen(
            [sys.executable, '-B', str(TOOLS / 'run_registry.py'), '--store', str(self.registry.directory),
             'run', '--id', run_id, '--kind', 'fixture', '--owner', 'test', '--',
             sys.executable, '-c', INSIDE, str(TOOLS), str(self.root), mode],
            stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
        self.processes.append(process)
        pid_file = self.root / 'nested.pid'
        self.wait_for(lambda: pid_file.exists() and pid_file.read_text())
        return process, int(pid_file.read_text())

    def closed(self, run_id):
        row = self.registry.read()['runs'][run_id]
        return row['status'] == 'stopped' and not any(R.live(a) for a in [row['scheduler']] + row['jobs'])

    def test_finds_the_run_whose_tree_holds_a_nested_process(self):
        _, nested = self.start('outer')
        self.assertEqual(W.run_containing(self.registry, nested), 'outer')
        self.assertIsNone(W.run_containing(self.registry, R.os.getpid()))

    def test_caller_outside_the_run_stops_it_in_place(self):
        process, nested = self.start('outside')
        self.assertEqual(W.stop_containing(nested, self.registry), ('outside', 'stopped'))
        self.assertTrue(self.closed('outside'))
        self.assertIsNotNone(process.wait(timeout=CEILING))

    def test_caller_inside_the_run_hands_the_stop_to_a_detached_process(self):
        process, _ = self.start('inside', 'helper')
        self.wait_for(lambda: self.closed('inside'))
        self.assertEqual((self.root / 'how').read_text(), 'detached')
        self.assertIsNotNone(process.wait(timeout=CEILING))

    def test_registry_refuses_a_stop_from_inside_its_own_run(self):
        process, _ = self.start('refused', 'direct')
        refused = self.root / 'refused'
        self.wait_for(refused.exists)
        self.assertIn('contains its caller', refused.read_text())
        self.assertEqual(self.registry.read()['runs']['refused']['status'], 'running')

    def test_process_outside_every_run_has_nothing_to_stop(self):
        self.assertEqual(W.stop_containing(R.os.getpid(), self.registry), (None, 'no_active_run'))


if __name__ == '__main__':
    unittest.main()
