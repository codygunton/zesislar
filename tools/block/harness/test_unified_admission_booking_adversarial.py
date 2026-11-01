"""Temporary-only controls for recorded bookings and aggregate sizing."""
import os
from pathlib import Path
import sys
import tempfile
import unittest

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE / 'code'))
import admission_memory as M


class LegacyBookingTests(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)
        fixture = self

        class Reader(M.ScopeReader):
            def shell(self, marker, *, owner=None):
                return fixture.observation()

        self.reader = Reader(proc=self.root / 'proc', cgroup_root=self.root / 'cgroup')
        self.group = self.reader.parent / f'zesuworkloads-aggregate{os.getuid()}p101r1.slice'
        self.group.mkdir(parents=True)
        (self.reader.parent / 'memory.max').write_text(str(M.SLICE_MAX_BYTES))
        (self.reader.parent / 'memory.swap.max').write_text('0')
        (self.group / 'memory.max').write_text(str(150 * M.GIB))
        (self.group / 'memory.swap.max').write_text('0')
        (self.group / 'memory.current').write_text('0')
        (self.group / 'cgroup.events').write_text('populated 1\n')
        self.markers = self.root / 'markers'
        self.markers.mkdir()

    def observation(self, live=0):
        info = self.group.stat()
        return dict(verified=True, aggregate_verified=True, scope=str(self.group),
                    device=info.st_dev, inode=info.st_ino, live_bytes=live * M.GIB)

    def marker(self, owner, booking, fence):
        path = self.markers / f'{owner}.fixture-generation-{owner}'
        path.write_text('confirmed\nwriter=\n' +
                        f'aggregate={self.group.name}\nowner_start=123\n' +
                        f'memory_claim_bytes={booking * M.GIB}\n' +
                        f'memory_fence_bytes={fence * M.GIB}\n')
        return path

    def inner(self, name, fence):
        path = self.group / f'zesudet-{name}.scope'
        path.mkdir()
        (path / 'memory.max').write_text(str(fence * M.GIB))
        (path / 'memory.swap.max').write_text('0')
        return path

    def booking(self, markers):
        return M.legacy_aggregate_booking(self.reader, self.observation(), markers)

    def account(self, booking, live):
        return M.evaluate({'legacy': booking}, 0, 300 * M.GIB,
                          observations={'legacy': self.observation(live)},
                          slice_max_bytes=175 * M.GIB, headroom_bytes=20 * M.GIB)

    def test_recorded_8_under_32_preserves_booking_and_live_growth(self):
        (self.group / 'memory.max').write_text(str(32 * M.GIB))
        marker = self.marker(101, 8, 32)
        self.inner('one', 32)
        result = self.booking([marker])
        self.assertEqual(result['booking_bytes'], 8 * M.GIB)
        self.assertEqual(result['recorded_booking_bytes'], 8 * M.GIB)
        low = self.account(result['booking_bytes'], 5)
        self.assertEqual(low['accounted_active_bytes'], 8 * M.GIB)
        self.assertEqual(low['unrealized_claim_bytes'], 3 * M.GIB)
        high = self.account(result['booking_bytes'], 12)
        self.assertEqual(high['accounted_active_bytes'], 12 * M.GIB)
        self.assertEqual(high['unrealized_claim_bytes'], 0)

    def test_recorded_64_under_150_does_not_become_150(self):
        marker = self.marker(101, 64, 64)
        self.inner('one', 64)
        result = self.booking([marker])
        self.assertEqual(result['booking_bytes'], 64 * M.GIB)
        low = self.account(result['booking_bytes'], 10)
        self.assertEqual(low['accounted_active_bytes'], 64 * M.GIB)
        self.assertEqual(low['unrealized_claim_bytes'], 54 * M.GIB)

    def test_nested_tokens_count_recorded_booking_once(self):
        first = self.marker(101, 8, 32)
        second = self.marker(102, 8, 32)
        self.inner('one', 32)
        self.inner('two', 32)
        result = self.booking([first, second])
        self.assertEqual(result['booking_bytes'], 8 * M.GIB)
        self.assertEqual(result['recorded_booking_bytes'], 8 * M.GIB)

    def test_recorded_booking_survives_token_end_until_aggregate_closes(self):
        (self.group / 'memory.max').write_text(str(32 * M.GIB))
        (self.group / 'memory.current').write_text(str(5 * M.GIB))
        marker = self.marker(101, 8, 32)
        result = self.booking([marker])
        marker.unlink()
        data = dict(legacy_aggregate_holds={'legacy': dict(
            aggregate={key: self.observation()[key]
                       for key in ('scope', 'device', 'inode')},
            fallback_bytes=result['booking_bytes'])})
        live = M.projection(data, {}, 0, 100 * M.GIB, reader=self.reader)
        self.assertEqual(live['active_claim_bytes'], 8 * M.GIB)
        self.assertEqual(live['unrealized_claim_bytes'], 3 * M.GIB)
        (self.group / 'cgroup.events').write_text('populated 0\n')
        closed = M.projection(data, {}, 0, 100 * M.GIB, reader=self.reader)
        self.assertEqual(closed['active_claim_bytes'], 0)

    def test_no_recorded_booking_sums_inner_fences_below_aggregate(self):
        self.inner('one', 64)
        self.inner('two', 64)
        result = self.booking([])
        self.assertEqual(result['booking_bytes'], 128 * M.GIB)
        self.assertFalse(result['recorded_booking_bytes'])

    def test_no_recorded_booking_never_exceeds_aggregate_fence(self):
        (self.group / 'memory.max').write_text(str(32 * M.GIB))
        self.inner('one', 32)
        self.inner('two', 32)
        result = self.booking([])
        self.assertEqual(result['booking_bytes'], 32 * M.GIB)


class NewAggregateLimitTests(unittest.TestCase):
    def test_new_6_gib_shell_does_not_inherit_150_gib(self):
        self.assertEqual(M.new_aggregate_limit(6 * M.GIB, 6 * M.GIB), 6 * M.GIB)

    def test_new_64_gib_shell_does_not_inherit_150_gib(self):
        self.assertEqual(M.new_aggregate_limit(64 * M.GIB, 64 * M.GIB), 64 * M.GIB)

    def test_measured_6_booking_preserves_64_inner_fence(self):
        self.assertEqual(M.new_aggregate_limit(64 * M.GIB, 6 * M.GIB), 64 * M.GIB)

    def test_explicit_canonical_family_fence_stays_exact(self):
        self.assertEqual(M.new_aggregate_limit(32 * M.GIB, 8 * M.GIB,
                                              explicit_limit_bytes=32 * M.GIB),
                         32 * M.GIB)

    def test_canonical_gate_fence_stays_exact(self):
        self.assertEqual(M.new_aggregate_limit(16 * M.GIB, 24 * M.GIB,
                                              gate_limit_bytes=120 * M.GIB),
                         120 * M.GIB)

    def test_conflicting_explicit_and_gate_fences_refuse(self):
        with self.assertRaises(ValueError):
            M.new_aggregate_limit(16 * M.GIB, 24 * M.GIB,
                                  explicit_limit_bytes=64 * M.GIB,
                                  gate_limit_bytes=120 * M.GIB)


if __name__ == '__main__':
    unittest.main()
