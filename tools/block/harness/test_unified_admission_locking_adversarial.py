"""Synthetic-process controls for the shared admission lock order."""
import fcntl
import hashlib
import json
import os
from pathlib import Path
import select
import subprocess
import sys
import tempfile
import unittest

HERE = Path(__file__).resolve().parent
CODE = HERE / 'code'
sys.path.insert(0, str(CODE))
import admission_memory as M


class UnifiedLockTests(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)
        self.gate = self.root / 'gate.lock'
        self.mutex = Path(str(self.gate) + '.mutex')
        self.mutex.touch()
        self.ledger = self.root / 'LEDGER.json'
        self.ledger.write_text(json.dumps(dict(fixed_claims={})))
        self.environment = dict(os.environ, ZESU_GATE_LOCK=str(self.gate),
                                PYTHONDONTWRITEBYTECODE='1')
        self.environment.pop('ZESU_GUARD_MUTEX_FD', None)

    def child(self, body, *, descriptor=None):
        environment = dict(self.environment)
        passed = ()
        if descriptor is not None:
            environment['ZESU_GUARD_MUTEX_FD'] = str(descriptor)
            passed = (descriptor,)
        source = ('import sys\nfrom pathlib import Path\n' +
                  f'sys.path.insert(0, {str(CODE)!r})\n' +
                  'import admission_memory as M\n' + body)
        process = subprocess.Popen([sys.executable, '-B', '-c', source],
                                   env=environment, pass_fds=passed,
                                   stdin=subprocess.PIPE,
                                   stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                                   text=True)
        self.addCleanup(self.close_child, process)
        return process

    @staticmethod
    def close_child(process):
        if process.poll() is None:
            process.kill()  # Only this test's synthetic child can reach this path.
        process.communicate()

    def finish(self, process):
        stdout, stderr = process.communicate(timeout=5)
        self.assertEqual(process.returncode, 0, stderr)
        return stdout

    def test_inherited_shell_lock_does_not_reopen_or_unlock_parent(self):
        with self.mutex.open('a') as parent:
            fcntl.flock(parent, fcntl.LOCK_EX)
            process = self.child('with M.guard_lock():\n    print("entered")\n',
                                 descriptor=parent.fileno())
            self.assertEqual(self.finish(process).strip(), 'entered')
            with self.mutex.open('a') as independent:
                with self.assertRaises(BlockingIOError):
                    fcntl.flock(independent, fcntl.LOCK_EX | fcntl.LOCK_NB)

    def test_inherited_descriptor_for_other_file_refuses(self):
        other = self.root / 'other.lock'
        with other.open('a') as stream:
            process = self.child(
                'try:\n'
                '    with M.guard_lock():\n'
                '        raise AssertionError("accepted unrelated descriptor")\n'
                'except ValueError:\n'
                '    print("refused")\n', descriptor=stream.fileno())
            self.assertEqual(self.finish(process).strip(), 'refused')

    def test_busy_inherited_description_refuses_without_waiting(self):
        with self.mutex.open('a') as parent, self.mutex.open('a') as other:
            fcntl.flock(parent, fcntl.LOCK_EX)
            process = self.child(
                'try:\n'
                '    with M.guard_lock():\n'
                '        raise AssertionError("accepted conflicting descriptor")\n'
                'except (ValueError, BlockingIOError):\n'
                '    print("refused")\n', descriptor=other.fileno())
            self.assertEqual(self.finish(process).strip(), 'refused')

    def test_canonical_waits_for_old_writer_before_taking_ledger(self):
        marker = self.root / 'old-token'
        with self.mutex.open('a') as old_writer:
            fcntl.flock(old_writer, fcntl.LOCK_EX)
            process = self.child(
                'print("ready", flush=True)\n'
                f'with M.ledger_transaction(Path({str(self.ledger)!r})):\n'
                f'    assert Path({str(marker)!r}).read_text() == "published"\n'
                '    print("saw old publication", flush=True)\n')
            self.assertEqual(process.stdout.readline().strip(), 'ready')
            # A reversed lock order would hold LEDGER while waiting for GATE.
            self.assertEqual(select.select([process.stdout], [], [], 0.1)[0], [])
            with self.ledger.with_name('LEDGER.lock').open('a') as ledger_lock:
                fcntl.flock(ledger_lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
            marker.write_text('published')
            fcntl.flock(old_writer, fcntl.LOCK_UN)
            self.assertEqual(self.finish(process).strip(), 'saw old publication')

    def test_canonical_transaction_holds_both_locks(self):
        process = self.child(
            f'with M.ledger_transaction(Path({str(self.ledger)!r})):\n'
            '    print("entered", flush=True)\n'
            '    sys.stdin.readline()\n')
        self.assertEqual(process.stdout.readline().strip(), 'entered')
        for path in (self.mutex, self.ledger.with_name('LEDGER.lock')):
            with self.subTest(path=path), path.open('a') as stream:
                with self.assertRaises(BlockingIOError):
                    fcntl.flock(stream, fcntl.LOCK_EX | fcntl.LOCK_NB)
        process.stdin.write('\n')
        process.stdin.flush()
        self.finish(process)


class LegacyRolloutTests(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)
        self.markers = self.root / 'markers'
        self.markers.mkdir()
        self.group = self.root / f'zesuworkloads-aggregate{os.getuid()}p101r1.slice'
        self.group.mkdir()
        (self.group / 'memory.max').write_text(str(64 * M.GIB))
        (self.group / 'memory.swap.max').write_text('0')
        self.source = self.root / 'resource_guard.sh'
        self.source.write_text('# Synthetic old writer. Never execute this file.\n')
        self.marker = self.markers / '101.old'
        self.publish_marker()
        self.owner = dict(pid=101, startticks=123)
        self.argv = ['bash', str(self.source), 'scope', 'fixture', '--', 'true']
        self.writer = dict(owner=self.owner, argv=self.argv,
                           source=dict(path=str(self.source), sha256=hashlib.sha256(
                               self.source.read_bytes()).hexdigest()),
                           marker=str(self.marker))
        fixture = self

        class Reader(M.ScopeReader):
            def __init__(self):
                self.uid = os.getuid()
                self.proc = fixture.root / 'proc'
                owner = self.proc / '101'
                owner.mkdir(parents=True)
                (owner / 'environ').write_bytes(
                    f'ZESU_AGGREGATE_SLICE={fixture.group.name}\0'.encode())

            def process(self, owner):
                if owner != fixture.owner:
                    raise ValueError('Unexpected synthetic owner.')
                return 1

            def argv(self, owner):
                self.process(owner)
                return list(fixture.argv)

            def shell(self, marker, *, owner=None):
                info = fixture.group.stat()
                return dict(verified=True, aggregate_verified=True,
                            scope=str(fixture.group), device=info.st_dev,
                            inode=info.st_ino, live_bytes=10 * M.GIB)

            def residual(self, bound):
                return self.shell(fixture.marker)

            def claim(self, data, key):
                return dict(verified=False, live_bytes=0)

            def slice_max(self):
                return 175 * M.GIB

        self.reader = Reader()
        self.data = dict(fixed_claims={}, shell_marker_directory=str(self.markers))

    def publish_marker(self):
        self.marker.write_text('confirmed\nowner_start=123\n' +
                               f'memory_claim_bytes={16 * M.GIB}\n' +
                               f'memory_fence_bytes={32 * M.GIB}\n')

    def rollout(self):
        return M.prepare_legacy_rollout(self.data, [self.writer], reader=self.reader)

    def test_old_publication_before_new_admission_keeps_aggregate_fence(self):
        protected = self.rollout()
        hold = next(iter(protected['legacy_aggregate_holds'].values()))
        self.assertEqual(hold['fallback_bytes'], 64 * M.GIB)
        result = M.projection(protected, {}, 20 * M.GIB, 100 * M.GIB,
                              reader=self.reader)
        self.assertEqual(result['active_claim_bytes'], 64 * M.GIB)
        self.assertEqual(result['unrealized_claim_bytes'], 54 * M.GIB)
        self.assertFalse(result['fits'])
        self.assertNotIn('legacy_aggregate_holds', self.data)

    def test_later_old_marker_cannot_escape_preexisting_fence_hold(self):
        protected = self.rollout()
        self.marker.unlink()
        before = M.projection(protected, {}, 16 * M.GIB, 100 * M.GIB,
                              reader=self.reader)
        self.assertTrue(before['fits'])
        self.publish_marker()
        after = M.projection(protected, {'new': 16 * M.GIB}, 0, 100 * M.GIB,
                             reader=self.reader)
        self.assertTrue(after['fits'])
        self.assertEqual(after['active_claim_bytes'], 80 * M.GIB)
        self.assertEqual(after['unrealized_claim_bytes'], 70 * M.GIB)
        self.assertEqual(after['accounted_active_bytes'], 80 * M.GIB)

    def test_old_writer_with_future_aggregate_refuses_rollout(self):
        self.argv = ['bash', str(self.source), 'batch', 'fixture', '--', 'true']
        self.writer['argv'] = list(self.argv)
        other = self.root / f'zesuworkloads-aggregate{os.getuid()}p999r1.slice'
        self.group.rename(other)
        self.group = other
        with self.assertRaisesRegex(ValueError, 'exact aggregate'):
            self.rollout()
        self.assertNotIn('legacy_aggregate_holds', self.data)


if __name__ == '__main__':
    unittest.main()
