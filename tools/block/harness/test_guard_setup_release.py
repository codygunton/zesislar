"""Rejected setup keeps admission closed and permits exact closed-leaf cleanup."""
import copy
import json
from pathlib import Path
import shutil
import unittest
from unittest.mock import patch

import test_owned_guard_scope as fixtures

M = fixtures.M


class GuardSetupRelease(unittest.TestCase):
    write = fixtures.OwnedGuardScope.write
    process = fixtures.OwnedGuardScope.process

    def setUp(self):
        fixtures.OwnedGuardScope.setUp(self)
        self.leaf.rmdir() if not list(self.leaf.iterdir()) else shutil.rmtree(self.leaf)
        self.leaf = self.reader.parent / 'zesudet-client-14-1.scope'
        self.leaf.mkdir()
        (self.leaf / 'memory.current').write_text('5')
        (self.leaf / 'cgroup.events').write_text('populated 1\n')
        self.process(self.owner, 12, ['bash', str(self.guard), 'scope', 'client'],
                     str(self.reader.parent.relative_to(self.reader.root)))
        self.process(self.actor, 14, self.argv, str(self.leaf.relative_to(self.reader.root)))
        (self.proc / '15/environ').write_bytes(b'')
        self.text = self.text.replace('aggregate=' + self.group.name, 'aggregate=')
        self.marker.write_text(self.text.replace('15\n', 'confirmed\n', 1))
        self.old_identity = M.ScopeReader.file_identity(self.marker.lstat())
        self.key = M.shell_key(self.marker)
        self.record = {'owner': self.owner, 'generation': self.generation,
                       'marker': str(self.marker), 'aggregate': None,
                       'guard_source': self.source, 'token_identity': self.old_identity}
        self.ledger.write_text(json.dumps({'fixed_claims': {self.key: 16 * M.GIB},
                                          'shell_claim_owners': {self.key: self.record}}))
        replacement = self.marker.with_name('replacement')
        replacement.write_text(self.text)
        replacement.chmod(0o600)
        replacement.replace(self.marker)
        self.assertNotEqual(M.ScopeReader.file_identity(self.marker.lstat()), self.old_identity)

    def read(self):
        return json.loads(self.ledger.read_text())

    def mark(self):
        return M.mark_shell(self.marker, ledger=self.ledger, reader=self.reader)

    def reject(self):
        with self.assertRaisesRegex(M.RejectedScopeSetup, 'standalone scope lacks its writer identity'):
            self.mark()

    def close(self):
        shutil.rmtree(self.proc / '15')
        (self.leaf / 'cgroup.events').write_text('populated 0\n')

    def release(self):
        return M.release_shell(self.marker, ledger=self.ledger, reader=self.reader)

    def test_setup_refuses_before_payload_and_releases_changed_inode_after_closure(self):
        payload_started = False
        try:
            self.mark()
            payload_started = True
        except M.RejectedScopeSetup:
            pass
        self.assertFalse(payload_started)
        data = self.read()
        record = data['shell_claim_owners'][self.key]
        self.assertEqual(data['fixed_claims'][self.key], 16 * M.GIB)
        self.assertEqual(record['token_identity'], list(M.ScopeReader.file_identity(self.marker.lstat())))
        self.assertNotEqual(record['token_identity'], list(self.old_identity))
        self.assertEqual(record['setup_failure']['schema'], 'rejected.guard.setup.v1')
        self.assertNotIn('guard_attestation', record)
        self.assertFalse(self.reader.compiler(self.marker)['verified'])
        self.assertFalse(self.reader.claim(data, self.key)['verified'])
        self.assertFalse(self.reader.owned_scope(self.marker, record['setup_failure'])['verified'])
        self.close()
        self.assertTrue(self.release())
        after = self.read()
        self.assertEqual(after['fixed_claims'][self.key], 0)
        self.assertEqual(M._shell_recovery_record(after, self.key, self.reader)[0], record)
        self.assertFalse(self.marker.exists())

    def test_live_leaf_retains_booking(self):
        self.reject()
        before = self.ledger.read_bytes()
        with self.assertRaisesRegex(ValueError, 'leaf is not closed'):
            self.release()
        self.assertEqual(self.ledger.read_bytes(), before)
        self.assertTrue(self.marker.exists())

    def test_live_actor_retains_booking_even_with_empty_leaf_report(self):
        self.reject()
        (self.leaf / 'cgroup.events').write_text('populated 0\n')
        before = self.ledger.read_bytes()
        with self.assertRaisesRegex(ValueError, 'actor is not closed'):
            self.release()
        self.assertEqual(self.ledger.read_bytes(), before)

    def test_replaced_leaf_retains_booking(self):
        self.reject()
        self.close()
        self.leaf.rename(self.leaf.with_name('retained-original'))
        self.leaf.mkdir()
        (self.leaf / 'cgroup.events').write_text('populated 0\n')
        before = self.ledger.read_bytes()
        with self.assertRaisesRegex(ValueError, 'leaf identity changed'):
            self.release()
        self.assertEqual(self.ledger.read_bytes(), before)

    def test_replaced_marker_retains_booking(self):
        self.reject()
        self.close()
        replacement = self.marker.with_name('replacement')
        replacement.write_bytes(self.marker.read_bytes())
        replacement.chmod(0o600)
        replacement.replace(self.marker)
        before = self.ledger.read_bytes()
        with self.assertRaisesRegex(ValueError, 'token identity changed'):
            self.release()
        self.assertEqual(self.ledger.read_bytes(), before)

    def test_new_guard_hardlink_keeps_mark_and_release(self):
        import os
        before = self.guard.lstat().st_ctime_ns
        os.link(self.guard, self.guard.with_name('dune-cache-link'))
        self.assertNotEqual(self.guard.lstat().st_ctime_ns, before)
        self.reject()
        self.close()
        self.assertTrue(self.release())
        self.assertEqual(self.read()['fixed_claims'][self.key], 0)

    def test_same_size_guard_content_change_refuses_mark(self):
        raw = bytearray(self.guard.read_bytes()); raw[-2] ^= 1
        self.guard.write_bytes(bytes(raw))
        before = self.ledger.read_bytes()
        with self.assertRaisesRegex(ValueError, 'guard source bytes changed'):
            self.mark()
        self.assertEqual(self.ledger.read_bytes(), before)

    def test_wrong_source_cannot_create_cleanup_evidence(self):
        self.guard.write_bytes(b'changed public guard')
        before = self.ledger.read_bytes()
        with self.assertRaisesRegex(ValueError, 'guard source bytes changed'):
            self.mark()
        self.assertEqual(self.ledger.read_bytes(), before)

    def test_wrong_command_cannot_create_cleanup_evidence(self):
        (self.proc / '15/cmdline').write_bytes(b'/fixture/client\0')
        before = self.ledger.read_bytes()
        with self.assertRaises(ValueError):
            self.mark()
        self.assertEqual(self.ledger.read_bytes(), before)

    def test_changed_owner_or_generation_cannot_create_cleanup_evidence(self):
        for old, new in (('owner_start=104', 'owner_start=999'),
                         (self.generation, '11111111-1111-1111-1111-111111111111')):
            with self.subTest(field=old):
                self.marker.write_text(self.text.replace(old, new))
                before = self.ledger.read_bytes()
                with self.assertRaises(ValueError):
                    self.mark()
                self.assertEqual(self.ledger.read_bytes(), before)

    def test_cleanup_publication_failure_preserves_claim(self):
        before = self.ledger.read_bytes()
        with patch.object(M, 'write_ledger', side_effect=OSError('injected write failure')):
            with self.assertRaises(OSError):
                self.mark()
        self.assertEqual(self.ledger.read_bytes(), before)
        self.assertEqual(self.read()['fixed_claims'][self.key], 16 * M.GIB)
        self.assertTrue(self.marker.exists())

    def test_marker_replacement_at_rejected_setup_handoff_retains_booking(self):
        validate = self.reader.scope_exec

        def replace_after_validation(*args):
            try:
                return validate(*args)
            except M.RejectedScopeSetup:
                replacement = self.marker.with_name('handoff-replacement')
                replacement.write_bytes(self.marker.read_bytes())
                replacement.chmod(0o600)
                replacement.replace(self.marker)
                raise

        before = self.ledger.read_bytes()
        with patch.object(self.reader, 'scope_exec', side_effect=replace_after_validation):
            with self.assertRaisesRegex(ValueError, 'token changed before publication'):
                self.mark()
        self.assertEqual(self.ledger.read_bytes(), before)
        self.assertEqual(self.read()['fixed_claims'][self.key], 16 * M.GIB)
        self.assertTrue(self.marker.exists())


if __name__ == '__main__':
    unittest.main()
