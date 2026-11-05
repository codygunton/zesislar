"""Check immutable release archives with private ledgers and fake process trees."""
import copy
import json
from pathlib import Path
import shutil
import threading
import unittest
from unittest.mock import patch

import test_unified_admission as fixtures
import admission_memory as M
import shell_archive as A


class ShellArchiveTests(unittest.TestCase):
    def setUp(self):
        self.fixture = fixtures.UnifiedAdmission()
        self.fixture.setUp()
        self.addCleanup(self.fixture.doCleanups)
        self.addCleanup(self.fixture.tearDown)
        self.f = self.fixture
        self.archive = self.f.root/'archive'
        self.f.confirm()
        self.key = M.shell_key(self.f.marker)

    def released(self):
        M.release_shell(self.f.marker, ledger=self.f.ledger, reader=self.f.reader)
        shutil.rmtree(self.f.reader.proc/'14')
        return self.f.read()

    def compact(self):
        return A.archive_released_shells(self.f.ledger, self.archive, reader=self.f.reader)

    def test_live_claim_stays_in_ledger(self):
        before = self.f.read()
        self.assertEqual(self.compact(), [])
        self.assertEqual(self.f.read(), before)

    def test_archived_records_and_admission_decision_stay_equal(self):
        before = self.released()
        expected = M.current_projection(8*M.GIB, 200*M.GIB,
                                        ledger=self.f.ledger, reader=self.f.reader)
        self.assertEqual(self.compact(), [self.key])
        after = self.f.read()
        self.assertNotIn(self.key, after['shell_claim_owners'])
        self.assertEqual(A.released_records(after, self.key, self.f.reader),
                         (before['shell_claim_owners'][self.key], before['shell_releases'][self.key]))
        self.assertEqual(M.current_projection(8*M.GIB, 200*M.GIB,
                                             ledger=self.f.ledger, reader=self.f.reader), expected)

    def test_failed_ledger_commit_leaves_authenticated_records_in_ledger(self):
        before = self.released()
        with patch.object(M, 'write_ledger', side_effect=OSError('injected ledger failure')):
            with self.assertRaises(OSError):
                self.compact()
        self.assertEqual(self.f.read(), before)
        self.assertTrue(A.document_path(self.archive, self.key).exists())
        self.assertEqual(self.compact(), [self.key])

    def test_failed_archive_publication_cannot_remove_ledger_records(self):
        before = self.released()
        with patch.object(A.os, 'link', side_effect=OSError('injected publication failure')):
            with self.assertRaises(OSError):
                self.compact()
        self.assertEqual(self.f.read(), before)
        self.assertFalse(A.document_path(self.archive, self.key).exists())
        self.assertEqual(self.compact(), [self.key])

    def test_concurrent_compaction_preserves_one_identical_release(self):
        before = self.released()
        results, errors = [], []
        def run():
            try:
                results.append(self.compact())
            except BaseException as error:
                errors.append(error)
        threads = [threading.Thread(target=run) for _ in range(2)]
        for thread in threads: thread.start()
        for thread in threads: thread.join(5)
        self.assertFalse(any(thread.is_alive() for thread in threads))
        self.assertEqual(errors, [])
        self.assertEqual(sorted(map(len, results)), [0, 1])
        self.assertEqual(A.released_records(self.f.read(), self.key, self.f.reader)[0],
                         before['shell_claim_owners'][self.key])

    def test_archive_tampering_refuses_but_ledger_records_take_precedence(self):
        before = self.released()
        self.compact()
        after = self.f.read()
        path = A.document_path(self.archive, self.key)
        changed = json.loads(path.read_text())
        changed['records']['shell_releases']['marker'] = '/wrong'
        path.write_text(json.dumps(changed))
        with self.assertRaises(ValueError):
            A.released_records(after, self.key, self.f.reader)
        for field in A.FIELDS:
            after[field] = copy.deepcopy(before.get(field, {}))
        self.assertEqual(A.released_records(after, self.key, self.f.reader),
                         (before['shell_claim_owners'][self.key], before['shell_releases'][self.key]))

    def test_partial_ledger_record_cannot_borrow_an_archived_release(self):
        before = self.released()
        self.compact()
        archived = self.f.read()
        for field in ('shell_claim_owners', 'shell_releases'):
            data = copy.deepcopy(archived)
            data[field] = copy.deepcopy(before[field])
            with self.assertRaisesRegex(ValueError, 'exact closed and released'):
                A.released_records(data, self.key, self.f.reader)

    def test_new_admission_and_archive_cannot_lose_each_others_records(self):
        self.released()
        owner = {'pid': 15, 'startticks': 104}
        self.f.process(owner, 12, ['guard', 'scope'],
                       str(self.f.group.relative_to(self.f.reader.root)))
        marker = self.f.tokens/'15.second-generation-1234'
        replacement = self.f.token('second')
        errors = []
        def confirm():
            try:
                M.confirm_shell(marker, replacement, 64*M.GIB, 200*M.GIB,
                                ledger=self.f.ledger, reader=self.f.reader)
            except BaseException as error:
                errors.append(error)
        thread = threading.Thread(target=confirm)
        thread.start()
        self.compact()
        thread.join(5)
        self.assertFalse(thread.is_alive())
        self.assertEqual(errors, [])
        data = self.f.read()
        self.assertEqual(data['fixed_claims'][M.shell_key(marker)], 64*M.GIB)
        self.assertIn(self.key, data['shell_archive'])
        self.assertTrue(marker.exists())

    def test_archived_generation_cannot_be_admitted_again(self):
        self.released()
        self.compact()
        self.f.process(self.f.pending, 12, ['guard', 'scope'],
                       str(self.f.group.relative_to(self.f.reader.root)))
        with self.assertRaisesRegex(ValueError, 'already exists'):
            self.f.confirm()
