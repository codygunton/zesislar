"""Check release storage with private ledgers and the existing fake kernel."""
import threading
import unittest
from unittest.mock import patch

import admission_memory as M
import shell_archive as A
import test_unified_admission as fixtures


class IncrementalShellArchiveTests(unittest.TestCase):
    def setUp(self):
        self.f = fixtures.UnifiedAdmission()
        self.f.setUp()
        self.addCleanup(self.f.doCleanups)
        self.f.confirm()
        self.key = M.shell_key(self.f.marker)
        self.before = self.f.read()

    def release(self):
        return M.release_shell(self.f.marker, ledger=self.f.ledger, reader=self.f.reader)

    def test_release_archives_the_exact_owner_and_preserves_live_scope_accounting(self):
        self.assertTrue(self.release())
        data = self.f.read()
        owner, released = A.released_records(data, self.key, self.f.reader)
        self.assertEqual(owner, self.before['shell_claim_owners'][self.key])
        self.assertEqual(released['owner'], owner['owner'])
        self.assertEqual(released['marker'], owner['marker'])
        self.assertEqual(data['fixed_claims'][self.key], 0)
        self.assertIn(self.key, data['shell_archive'])
        self.assertNotIn(self.key, data['shell_claim_owners'])
        self.assertFalse(self.f.marker.exists())
        # The aggregate stays populated after its compiler token ends.
        decision = M.projection(data, M.ledger_claims(data), 0, 200*M.GIB, reader=self.f.reader)
        self.assertEqual(decision['accounted_active_bytes'], 64*M.GIB)

    def test_failed_release_write_retains_booking_and_allows_dead_owner_retry(self):
        with patch.object(M, 'write_ledger', side_effect=OSError('injected ledger failure')):
            with self.assertRaises(OSError):
                self.release()
        self.assertEqual(self.f.read(), self.before)
        self.assertTrue(self.f.marker.exists())
        published = list((self.f.root/'released-shell-archive').glob('*.json'))
        self.assertEqual(len(published), 1)
        orphan_bytes = published[0].read_bytes()
        # Recovery changes the release metadata; an orphan archive must not block it.
        import shutil
        shutil.rmtree(self.f.proc/'14')
        (self.f.group/'cgroup.events').write_text('populated 0\n')
        self.assertTrue(M.recover_dead_shell(self.f.marker, ledger=self.f.ledger, reader=self.f.reader))
        data = self.f.read()
        owner, released = A.released_records(data, self.key, self.f.reader)
        self.assertEqual(owner, self.before['shell_claim_owners'][self.key])
        self.assertTrue(released['dead_owner_recovery'])
        self.assertEqual(data['fixed_claims'][self.key], 0)
        self.assertEqual(published[0].read_bytes(), orphan_bytes)
        self.assertEqual(len(list((self.f.root/'released-shell-archive').glob('*.json'))), 2)

    def test_archive_publication_failure_cannot_lose_the_release_record(self):
        with patch.object(A.os, 'link', side_effect=OSError('injected archive failure')):
            with self.assertRaises(OSError):
                self.release()
        data = self.f.read()
        if data['fixed_claims'][self.key]:
            self.assertEqual(data, self.before)
            self.assertTrue(self.f.marker.exists())
        else:
            owner, released = A.released_records(data, self.key, self.f.reader)
            self.assertEqual(owner, self.before['shell_claim_owners'][self.key])
            self.assertEqual(released['owner'], owner['owner'])
        if self.f.marker.exists():
            self.assertTrue(self.release())
        self.assertEqual(self.f.read()['fixed_claims'][self.key], 0)

    def test_concurrent_reader_sees_a_complete_authoritative_record(self):
        publishing, proceed, observed = threading.Event(), threading.Event(), threading.Event()
        errors, snapshots = [], []
        original = A.publish
        def paused(*args, **kwargs):
            publishing.set()
            if not proceed.wait(5):
                raise TimeoutError('The archive control did not resume.')
            return original(*args, **kwargs)
        def release():
            try:
                self.release()
            except BaseException as error:
                errors.append(error)
        def read():
            try:
                with M.ledger_transaction(self.f.ledger) as data:
                    snapshots.append((data['fixed_claims'][self.key],
                                      A.released_records(data, self.key, self.f.reader)))
                    observed.set()
            except BaseException as error:
                errors.append(error)
        with patch.object(A, 'publish', paused):
            writer = threading.Thread(target=release)
            reader = None
            writer.start()
            try:
                self.assertTrue(publishing.wait(5))
                reader = threading.Thread(target=read)
                reader.start()
                self.assertFalse(observed.wait(0.05))
            finally:
                proceed.set()
                writer.join(5)
            if reader is not None:
                reader.join(5)
        self.assertEqual(errors, [])
        self.assertTrue(observed.is_set())
        self.assertEqual(snapshots[0][0], 0)
        self.assertEqual(snapshots[0][1][0], self.before['shell_claim_owners'][self.key])

    def test_same_content_retry_reuses_the_published_document(self):
        self.release()
        data = self.f.read()
        directory = data['shell_archive_directory']
        reference = data['shell_archive'][self.key]
        records = A.archive_record(data, self.key, self.f.reader)
        first = A.document_path(directory, self.key, reference)
        identity = self.f.reader.file_identity(first.lstat())
        self.assertEqual(A.publish(directory, self.key, records), reference)
        self.assertEqual(self.f.reader.file_identity(first.lstat()), identity)
        self.assertEqual(len(list(first.parent.glob('*.json'))), 1)

    def test_authenticated_legacy_key_file_stays_readable(self):
        self.release()
        data = self.f.read()
        expected = A.released_records(data, self.key, self.f.reader)
        directory = data['shell_archive_directory']
        content = A.document_path(directory, self.key, data['shell_archive'][self.key])
        legacy = A.document_path(directory, self.key)
        content.rename(legacy)
        self.assertEqual(A.released_records(data, self.key, self.f.reader), expected)
        legacy.write_text('{}')
        with self.assertRaisesRegex(ValueError, 'archive identity changed'):
            A.released_records(data, self.key, self.f.reader)

    def test_tampered_content_file_cannot_fall_back_to_a_valid_legacy_file(self):
        self.release()
        data = self.f.read()
        directory = data['shell_archive_directory']
        content = A.document_path(directory, self.key, data['shell_archive'][self.key])
        legacy = A.document_path(directory, self.key)
        legacy.write_bytes(content.read_bytes())
        content.write_text('{}')
        with self.assertRaisesRegex(ValueError, 'archive identity changed'):
            A.released_records(data, self.key, self.f.reader)

    def seed_old_releases(self):
        import copy
        data = self.f.read()
        keys = []
        for name, pid in [('closed', 999999), ('live', 14)]:
            marker = self.f.tokens/name
            key = M.shell_key(marker)
            owner = copy.deepcopy(data['shell_claim_owners'][self.key])
            owner['marker'] = str(marker)
            owner['owner'] = {'pid': pid, 'startticks': 104}
            owner.pop('leaf', None)
            data['shell_claim_owners'][key] = owner
            data.setdefault('shell_releases', {})[key] = {
                'owner': owner['owner'], 'marker': owner['marker']}
            data['fixed_claims'][key] = 0
            keys.append(key)
        M.write_ledger(self.f.ledger, data)
        return keys

    def test_threshold_compacts_closed_records_and_retains_live_records(self):
        closed, live = self.seed_old_releases()
        before = self.f.read()['shell_claim_owners'][closed]
        with patch.object(M, 'SHELL_ARCHIVE_THRESHOLD_BYTES', 0):
            self.release()
        data = self.f.read()
        self.assertEqual(A.released_records(data, closed, self.f.reader)[0], before)
        self.assertNotIn(closed, data['shell_claim_owners'])
        self.assertIn(live, data['shell_claim_owners'])
        self.assertNotIn(live, data['shell_archive'])

    def test_below_threshold_retains_old_records(self):
        closed, live = self.seed_old_releases()
        with patch.object(M, 'SHELL_ARCHIVE_THRESHOLD_BYTES', self.f.ledger.stat().st_size):
            self.release()
        data = self.f.read()
        self.assertIn(closed, data['shell_claim_owners'])
        self.assertIn(live, data['shell_claim_owners'])
        self.assertEqual(set(data['shell_archive']), {self.key})

    def test_threshold_retains_a_changed_leaf_without_blocking_other_records(self):
        closed, changed = self.seed_old_releases()
        data = self.f.read()
        data['shell_claim_owners'][changed]['owner'] = {'pid': 999998, 'startticks': 104}
        data['shell_releases'][changed]['owner'] = data['shell_claim_owners'][changed]['owner']
        data['shell_claim_owners'][changed]['leaf'] = {'scope': str(self.f.group), 'device': -1, 'inode': -1}
        M.write_ledger(self.f.ledger, data)
        with patch.object(M, 'SHELL_ARCHIVE_THRESHOLD_BYTES', 0):
            self.release()
        data = self.f.read()
        self.assertIn(closed, data['shell_archive'])
        self.assertIn(changed, data['shell_claim_owners'])
        self.assertNotIn(changed, data['shell_archive'])
