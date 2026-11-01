"""Temporary-only controls for retained bookings and pending shell tokens."""
import copy
import json
import os
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE / 'code'))
import admission_memory as M


def sample(live=10, *, scope='/fixture/aggregate', inode=2):
    return dict(verified=True, aggregate_verified=True, scope=scope,
                device=1, inode=inode, live_bytes=live * M.GIB)


class FixtureReader:
    """Supply all kernel observations without consulting a live process."""
    uid = os.getuid()
    file_identity = staticmethod(M.ScopeReader.file_identity)

    def __init__(self):
        self.observation = sample()
        self.closed = False

    def claim(self, data, key):
        return copy.deepcopy(self.observation)

    def residual(self, bound):
        if self.closed:
            return dict(verified=True, closed=True, live_bytes=0)
        return copy.deepcopy(self.observation)

    def slice_max(self):
        return 175 * M.GIB

    def process(self, actor):
        return 1

    def shell(self, marker, *, owner=None):
        return copy.deepcopy(self.observation)

    def directory(self, path):
        info = Path(path).stat()
        return info.st_dev, info.st_ino


class RetainedBookingTests(unittest.TestCase):
    def setUp(self):
        self.reader = FixtureReader()
        self.data = dict(shell_aggregate_holds={
            'held': dict(aggregate={key: sample()[key]
                                   for key in ('scope', 'device', 'inode')},
                         fallback_bytes=64 * M.GIB)})

    def project(self, new=0):
        return M.projection(self.data, {}, new * M.GIB, 100 * M.GIB,
                            reader=self.reader)

    def test_64_gib_booking_survives_10_gib_usage(self):
        result = self.project(20)
        self.assertEqual(result['active_claim_bytes'], 64 * M.GIB)
        self.assertEqual(result['accounted_active_bytes'], 64 * M.GIB)
        self.assertEqual(result['unrealized_claim_bytes'], 54 * M.GIB)
        self.assertFalse(result['fits'])

    def test_usage_above_booking_remains_accounted(self):
        self.reader.observation = sample(80)
        result = self.project()
        self.assertEqual(result['accounted_active_bytes'], 80 * M.GIB)
        self.assertEqual(result['unrealized_claim_bytes'], 0)

    def test_unverified_aggregate_keeps_full_booking(self):
        self.reader.observation = dict(verified=False, live_bytes=0)
        result = self.project()
        self.assertEqual(result['accounted_active_bytes'], 64 * M.GIB)
        self.assertEqual(result['unrealized_claim_bytes'], 64 * M.GIB)

    def test_exact_aggregate_closure_releases_hold(self):
        self.reader.closed = True
        result = self.project(20)
        self.assertEqual(result['active_claim_bytes'], 0)
        self.assertTrue(result['fits'])


class PendingGroupingTests(unittest.TestCase):
    def evaluate(self, claims, observations, **kwargs):
        return M.evaluate(claims, 0, 300 * M.GIB, observations=observations,
                          slice_max_bytes=175 * M.GIB,
                          headroom_bytes=20 * M.GIB, **kwargs)

    def test_pending_tokens_keep_largest_approved_aggregate_booking(self):
        result = self.evaluate({'first': 64 * M.GIB, 'second': 16 * M.GIB},
                               {'first': sample(0), 'second': sample(0)})
        self.assertEqual(result['active_claim_bytes'], 64 * M.GIB)
        self.assertEqual(result['unrealized_claim_bytes'], 64 * M.GIB)
        self.assertEqual(result['raw_claim_bytes'], 80 * M.GIB)

    def test_new_pending_token_cannot_reduce_existing_booking(self):
        result = M.evaluate({'first': 64 * M.GIB}, 16 * M.GIB, 300 * M.GIB,
                            observations={'first': sample(0)},
                            new_observation=sample(0), slice_max_bytes=175 * M.GIB,
                            headroom_bytes=20 * M.GIB)
        self.assertEqual(result['active_claim_bytes'], 64 * M.GIB)
        self.assertEqual(result['unrealized_claim_bytes'], 64 * M.GIB)

    def test_distinct_pending_aggregates_remain_additive(self):
        result = self.evaluate({'first': 64 * M.GIB, 'second': 64 * M.GIB},
                               {'first': sample(0),
                                'second': sample(0, scope='/fixture/other', inode=3)})
        self.assertEqual(result['active_claim_bytes'], 128 * M.GIB)
        self.assertEqual(result['unrealized_claim_bytes'], 128 * M.GIB)

    def test_unverified_pending_token_cannot_share_credit(self):
        result = self.evaluate({'first': 64 * M.GIB, 'second': 64 * M.GIB},
                               {'first': sample(10),
                                'second': dict(verified=False, live_bytes=0)})
        self.assertEqual(result['active_claim_bytes'], 128 * M.GIB)
        self.assertEqual(result['unrealized_claim_bytes'], 118 * M.GIB)


class TokenReleaseTests(unittest.TestCase):
    generation = 'fixture-generation-0001'

    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        environment = dict(os.environ, ZESU_GATE_LOCK=str(self.root / 'gate.lock'))
        environment.pop('ZESU_GUARD_MUTEX_FD', None)
        self.environment = patch.dict(os.environ, environment, clear=True)
        self.environment.start()
        self.addCleanup(self.environment.stop)
        self.ledger = self.root / 'LEDGER.json'
        self.reader = FixtureReader()
        self.data = dict(fixed_claims={}, shell_claim_owners={})

    def token(self, pid, booking, *, numeric=False):
        marker = self.root / f'{pid}.token'
        marker.write_text(('999\n' if numeric else 'confirmed\n') +
                          'owner_start=123\nchild_start=124\n' +
                          f'reservation_generation={self.generation}\n')
        key = M.shell_key(marker)
        self.data['fixed_claims'][key] = booking * M.GIB
        self.data['shell_claim_owners'][key] = dict(
            owner=dict(pid=pid, startticks=123), marker=str(marker),
            generation=self.generation,
            token_identity=list(self.reader.file_identity(marker.lstat())),
            aggregate={name: sample()[name] for name in ('scope', 'device', 'inode')})
        return marker, key

    def save(self):
        self.ledger.write_text(json.dumps(self.data))

    def test_approved_measured_booking_stays_below_unchanged_fence(self):
        directory = self.root / 'markers'
        directory.mkdir()
        marker = directory / f'101.{self.generation}'
        replacement = self.root / 'replacement'
        replacement.write_text('confirmed\nowner_start=123\n' +
                               f'reservation_generation={self.generation}\n' +
                               f'memory_claim_bytes={16 * M.GIB}\n' +
                               f'memory_fence_bytes={64 * M.GIB}\n')
        self.data['shell_marker_directory'] = str(directory)
        self.reader.observation = sample(0)
        self.save()
        result = M.confirm_shell(marker, replacement, 16 * M.GIB, 100 * M.GIB,
                                 ledger=self.ledger, reader=self.reader)
        self.assertTrue(result['fits'])
        data = json.loads(self.ledger.read_text())
        key = M.shell_key(marker)
        self.assertEqual(data['fixed_claims'][key], 16 * M.GIB)
        rows = M.shell_rows(data, self.reader)
        self.assertEqual(rows[key][0], 16 * M.GIB)
        self.assertIn(f'memory_fence_bytes={64 * M.GIB}', marker.read_text())

    def test_released_token_path_cannot_name_a_new_reservation(self):
        marker, key = self.token(101, 64)
        marker.unlink()
        self.data['fixed_claims'][key] = 0
        self.save()
        replacement = self.root / 'replacement'
        replacement.write_text('confirmed\nowner_start=456\n' +
                               f'reservation_generation={self.generation}\n' +
                               f'memory_claim_bytes={16 * M.GIB}\n' +
                               f'memory_fence_bytes={64 * M.GIB}\n')
        before = self.ledger.read_bytes()
        with self.assertRaisesRegex(ValueError, 'already exists'):
            M.confirm_shell(marker, replacement, 16 * M.GIB, 100 * M.GIB,
                            ledger=self.ledger, reader=self.reader)
        self.assertEqual(self.ledger.read_bytes(), before)
        self.assertFalse(marker.exists())
        self.assertTrue(replacement.exists())

    def test_identical_bytes_replacement_cannot_release_original_token(self):
        marker, _ = self.token(101, 64)
        self.save()
        before = self.ledger.read_bytes()
        original = marker.read_bytes()
        replacement = self.root / 'replacement'
        replacement.write_bytes(original)
        os.replace(replacement, marker)
        with self.assertRaisesRegex(ValueError, 'token identity changed'):
            M.release_shell(marker, ledger=self.ledger, reader=self.reader)
        self.assertEqual(self.ledger.read_bytes(), before)
        self.assertEqual(marker.read_bytes(), original)

    def test_changed_generation_refuses_even_with_current_stat_binding(self):
        marker, key = self.token(101, 64)
        marker.write_text(marker.read_text().replace(self.generation,
                                                    'fixture-generation-0002'))
        self.data['shell_claim_owners'][key]['token_identity'] = list(
            self.reader.file_identity(marker.lstat()))
        self.save()
        before = self.ledger.read_bytes()
        with self.assertRaisesRegex(ValueError, 'release owner differs'):
            M.release_shell(marker, ledger=self.ledger, reader=self.reader)
        self.assertEqual(self.ledger.read_bytes(), before)
        self.assertTrue(marker.exists())

    def test_sibling_release_cannot_reduce_retained_booking(self):
        first, first_key = self.token(101, 64)
        second, second_key = self.token(102, 16)
        self.save()
        self.assertTrue(M.release_shell(first, ledger=self.ledger, reader=self.reader))
        data = json.loads(self.ledger.read_text())
        self.assertEqual(data['fixed_claims'][second_key], 16 * M.GIB)
        result = M.projection(data, data['fixed_claims'], 0, 100 * M.GIB,
                              reader=self.reader)
        self.assertEqual(result['active_claim_bytes'], 64 * M.GIB)
        self.assertTrue(M.release_shell(second, ledger=self.ledger, reader=self.reader))
        data = json.loads(self.ledger.read_text())
        self.assertEqual(data['fixed_claims'][first_key], 0)
        self.assertEqual(data['fixed_claims'][second_key], 0)
        result = M.projection(data, data['fixed_claims'], 0, 100 * M.GIB,
                              reader=self.reader)
        self.assertEqual(result['active_claim_bytes'], 64 * M.GIB)
        self.assertEqual(result['unrealized_claim_bytes'], 54 * M.GIB)

    def test_live_leaf_refuses_release_despite_closed_wrapper(self):
        marker, key = self.token(101, 64, numeric=True)
        leaf = self.root / 'leaf'
        leaf.mkdir()
        (leaf / 'cgroup.events').write_text('populated 1\n')
        info = leaf.stat()
        self.data['shell_claim_owners'][key]['leaf'] = dict(
            scope=str(leaf), device=info.st_dev, inode=info.st_ino)
        self.save()
        before = self.ledger.read_bytes()
        with self.assertRaisesRegex(ValueError, 'leaf is not closed'):
            M.release_shell(marker, ledger=self.ledger, reader=self.reader)
        self.assertEqual(self.ledger.read_bytes(), before)
        self.assertTrue(marker.exists())

    def test_closed_leaf_cannot_release_unknown_known_aggregate(self):
        marker, key = self.token(101, 64, numeric=True)
        leaf = self.root / 'leaf'
        leaf.mkdir()
        (leaf / 'cgroup.events').write_text('populated 0\n')
        info = leaf.stat()
        self.data['shell_claim_owners'][key]['leaf'] = dict(
            scope=str(leaf), device=info.st_dev, inode=info.st_ino)
        self.reader.proc = self.root / 'proc'
        self.reader.proc.mkdir()
        self.reader.observation = dict(verified=False, live_bytes=0,
                                       reason='synthetic unknown aggregate closure')
        self.save()
        before = self.ledger.read_bytes()
        token = marker.read_bytes()
        with self.assertRaisesRegex(ValueError, 'aggregate closure cannot be authenticated'):
            M.release_shell(marker, ledger=self.ledger, reader=self.reader)
        self.assertEqual(self.ledger.read_bytes(), before)
        self.assertEqual(marker.read_bytes(), token)
        self.assertEqual(json.loads(self.ledger.read_text())['fixed_claims'][key],
                         64 * M.GIB)


if __name__ == '__main__':
    unittest.main()
