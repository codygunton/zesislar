"""Stale-token recovery retains all live owners and live scope bookings."""
import shutil
import unittest
from unittest.mock import patch

import test_dead_shell_recovery as F

M = F.M


class StaleShellRecovery(unittest.TestCase):
    def setUp(self):
        self.fixture = F.Fixtures.UnifiedAdmission()
        self.fixture.setUp()
        self.addCleanup(self.fixture.doCleanups)
        self.fixture.confirm()

    def recover(self):
        f = self.fixture
        return M.recover_stale_shell(f.marker, ledger=f.ledger, reader=f.reader)

    def close(self):
        f = self.fixture
        for p in f.proc.iterdir():
            if p.is_dir():
                shutil.rmtree(p)
        (f.group / 'cgroup.events').write_text('populated 0\n')

    def test_missing_token_releases_dead_closed_booking_with_audit(self):
        f = self.fixture
        self.close()
        f.marker.unlink()
        self.assertTrue(self.recover())
        data = f.read()
        key = M.shell_key(f.marker)
        self.assertEqual(data['fixed_claims'][key], 0)
        self.assertEqual(M._shell_recovery_record(data, key, f.reader)[1]['released_bytes'], 64 * M.GIB)
        self.assertTrue(M._shell_recovery_record(data, key, f.reader)[1]['stale_owner_recovery'])
        self.assertIsNone(M._shell_recovery_record(data, key, f.reader)[1]['observed_token_identity'])
        self.assertFalse(self.recover())

    def test_changed_token_stays_on_disk(self):
        f = self.fixture
        self.close()
        f.marker.write_text('replacement\n')
        self.assertTrue(self.recover())
        self.assertEqual(f.marker.read_text(), 'replacement\n')

    def test_live_owner_refuses_without_writing(self):
        f = self.fixture
        f.marker.unlink()
        before = f.ledger.read_bytes()
        with self.assertRaisesRegex(ValueError, 'still live'):
            self.recover()
        self.assertEqual(f.ledger.read_bytes(), before)

    def test_exact_token_uses_the_existing_release_route(self):
        self.close()
        with self.assertRaisesRegex(ValueError, 'missing or changed'):
            self.recover()

    def test_populated_scope_refuses(self):
        f = self.fixture
        self.close()
        f.marker.unlink()
        (f.group / 'cgroup.events').write_text('populated 1\n')
        with self.assertRaisesRegex(ValueError, 'still populated'):
            self.recover()

    def test_process_membership_refuses_even_with_empty_events(self):
        f = self.fixture
        self.close()
        f.marker.unlink()
        f.process({'pid': 99, 'startticks': 555}, 1, ['compiler'],
                  str(f.group.relative_to(f.reader.root)))
        with self.assertRaisesRegex(ValueError, 'still uses.*cgroup'):
            self.recover()

    def test_replaced_scope_refuses(self):
        f = self.fixture
        self.close()
        f.marker.unlink()
        f.group.rename(f.group.with_name('old-scope'))
        f.group.mkdir()
        (f.group / 'cgroup.events').write_text('populated 0\n')
        with self.assertRaisesRegex(ValueError, 'identity changed'):
            self.recover()

    def test_write_failure_keeps_the_booking(self):
        f = self.fixture
        self.close()
        f.marker.unlink()
        before = f.ledger.read_bytes()
        with patch.object(M, 'write_ledger', side_effect=OSError('write failed')):
            with self.assertRaises(OSError):
                self.recover()
        self.assertEqual(f.ledger.read_bytes(), before)

    def test_enumeration_recovers_a_marker_removed_by_an_older_guard(self):
        f = self.fixture
        self.close()
        # This models the older live_reservations dead-owner removal.
        f.marker.unlink()
        rows = M.recover_stale_shells(ledger=f.ledger, reader=f.reader)
        self.assertEqual(rows, [{'key': M.shell_key(f.marker), 'released': True}])
        self.assertEqual(M.recover_stale_shells(ledger=f.ledger, reader=f.reader), [])

    def test_reused_owner_pid_with_another_starttime_can_release(self):
        f = self.fixture
        self.close()
        f.marker.unlink()
        f.process({'pid': 14, 'startticks': 999}, 1, ['unrelated'], 'other.scope')
        self.assertTrue(self.recover())

    def test_populated_leaf_refuses_even_after_the_aggregate_closes(self):
        f = self.fixture
        self.close()
        f.marker.unlink()
        leaf = f.group / 'compiler.scope'
        leaf.mkdir()
        (leaf / 'cgroup.events').write_text('populated 1\n')
        info = leaf.stat()
        data = f.read()
        data['shell_claim_owners'][M.shell_key(f.marker)]['leaf'] = {
            'scope': str(leaf), 'device': info.st_dev, 'inode': info.st_ino}
        f.save(data)
        with self.assertRaisesRegex(ValueError, 'still populated'):
            self.recover()

    def test_enumeration_leaves_a_live_owner_with_a_missing_marker(self):
        f = self.fixture
        f.marker.unlink()
        before = f.ledger.read_bytes()
        self.assertEqual(M.recover_stale_shells(ledger=f.ledger, reader=f.reader), [])
        self.assertEqual(f.ledger.read_bytes(), before)

    def test_enumeration_keeps_a_populated_scope_and_reports_its_reason(self):
        f = self.fixture
        self.close()
        f.marker.unlink()
        (f.group / 'cgroup.events').write_text('populated 1\n')
        rows = M.recover_stale_shells(ledger=f.ledger, reader=f.reader)
        self.assertFalse(rows[0]['released'])
        self.assertIn('populated', rows[0]['reason'])
        self.assertNotEqual(f.read()['fixed_claims'][M.shell_key(f.marker)], 0)


if __name__ == '__main__':
    unittest.main()
