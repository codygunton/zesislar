"""Recover only exact ended owners without weakening compiler-leaf checks."""
from pathlib import Path
import shutil
import sys
import unittest

HERE = Path(__file__).resolve().parent
sys.path[:0] = [str(HERE / 'code'), str(HERE)]
import admission_memory as M
import test_unified_admission as Fixtures


class DeadOwnerRecoveryTests(unittest.TestCase):
    def setUp(self):
        self.fixture = Fixtures.UnifiedAdmission()
        self.fixture.setUp()
        self.addCleanup(self.fixture.doCleanups)
        self.fixture.confirm()

    def recover(self):
        f = self.fixture
        return M.recover_dead_shell(f.marker, ledger=f.ledger, reader=f.reader)

    def end_owner(self):
        shutil.rmtree(self.fixture.proc / '14')

    def test_live_owner_keeps_its_exact_reservation(self):
        f = self.fixture
        before = f.ledger.read_bytes()
        with self.assertRaisesRegex(ValueError, 'owner is still live'):
            self.recover()
        self.assertEqual(f.ledger.read_bytes(), before)
        self.assertTrue(f.marker.exists())

    def test_dead_owner_releases_token_but_retains_populated_aggregate(self):
        f = self.fixture
        self.end_owner()
        self.assertTrue(self.recover())
        data = f.read()
        self.assertFalse(f.marker.exists())
        self.assertEqual(data['fixed_claims'][M.shell_key(f.marker)], 0)
        result = M.projection(data, M.ledger_claims(data), 0, 200 * M.GIB, reader=f.reader)
        self.assertEqual(result['accounted_active_bytes'], 64 * M.GIB)
        self.assertTrue(M._shell_recovery_record(data, M.shell_key(f.marker), f.reader)[1]['dead_owner_recovery'])

    def test_dead_owner_and_closed_aggregate_release_booking(self):
        f = self.fixture
        self.end_owner()
        (f.group / 'cgroup.events').write_text('populated 0\n')
        self.assertTrue(self.recover())
        data = f.read()
        result = M.projection(data, M.ledger_claims(data), 0, 200 * M.GIB, reader=f.reader)
        self.assertEqual(result['accounted_active_bytes'], 0)

    def test_changed_generation_stays_refused_after_owner_ends(self):
        f = self.fixture
        self.end_owner()
        f.marker.write_text(f.marker.read_text().replace('fixture-generation-1234', 'wrong-generation'))
        before = f.ledger.read_bytes()
        with self.assertRaisesRegex(ValueError, 'owner differs from its token'):
            self.recover()
        self.assertEqual(f.ledger.read_bytes(), before)
        self.assertTrue(f.marker.exists())


    def test_incomplete_identity_with_existing_scope_stays_refused(self):
        f = self.fixture
        self.interrupt_confirmation()
        self.end_owner()
        f.marker.write_text(f.marker.read_text() + 'changed=yes\n')
        before = f.ledger.read_bytes()
        with self.assertRaisesRegex(ValueError, 'scope is still present'):
            self.recover()
        self.assertEqual(f.ledger.read_bytes(), before)
        self.assertTrue(f.marker.exists())

    def test_dead_wrapper_cannot_release_populated_compiler_leaf(self):
        f = self.fixture
        f.marker.write_text(f.marker.read_text().replace('confirmed\n', '99\n') + 'child_start=999\n')
        leaf = f.group / 'compiler.scope'
        leaf.mkdir()
        (leaf / 'cgroup.events').write_text('populated 1\n')
        info = leaf.stat()
        data = f.read()
        record = data['shell_claim_owners'][M.shell_key(f.marker)]
        record['token_identity'] = list(f.reader.file_identity(f.marker.lstat()))
        record['leaf'] = dict(scope=str(leaf), device=info.st_dev, inode=info.st_ino)
        f.save(data)
        self.end_owner()
        before = f.ledger.read_bytes()
        with self.assertRaisesRegex(ValueError, 'leaf is not closed'):
            self.recover()
        self.assertEqual(f.ledger.read_bytes(), before)

    def test_complete_generation_mismatch_refuses_with_all_actors_and_scopes_absent(self):
        f = self.fixture
        self.end_owner()
        shutil.rmtree(f.group)
        f.marker.write_text(f.marker.read_text().replace('fixture-generation-1234', 'wrong-generation'))
        before = f.ledger.read_bytes()
        with self.assertRaisesRegex(ValueError, 'owner differs from its token'):
            self.recover()
        self.assertEqual(f.ledger.read_bytes(), before)
        self.assertTrue(f.marker.exists())

    def test_complete_replaced_token_uses_authenticated_main_release(self):
        f = self.fixture
        self.end_owner()
        f.marker.write_text(f.marker.read_text() + 'changed=yes\n')
        self.assertTrue(self.recover())
        data = f.read()
        key = M.shell_key(f.marker)
        self.assertTrue(M._shell_recovery_record(data, key, f.reader)[1]['dead_owner_recovery'])
        self.assertFalse(f.marker.exists())
        result = M.projection(data, M.ledger_claims(data), 0, 200*M.GIB, reader=f.reader)
        self.assertEqual(result['accounted_active_bytes'], 64*M.GIB)

    def orphan(self):
        f = self.fixture
        data = f.read()
        key = M.shell_key(f.marker)
        data['shell_claim_owners'].pop(key)
        f.save(data)
        return data

    def test_unadmitted_orphan_requires_absent_owner_actor_and_scope(self):
        f = self.fixture
        self.orphan()
        self.end_owner()
        shutil.rmtree(f.group)
        self.assertTrue(self.recover())
        data = f.read()
        audit = data['shell_recovery_audits'][M.shell_key(f.marker)]
        self.assertEqual(audit['route'], 'unadmitted_orphan')
        self.assertEqual(audit['owner'], f.pending)
        self.assertFalse(f.marker.exists())
        self.assertEqual(data['fixed_claims'][M.shell_key(f.marker)], 0)

    def test_unadmitted_orphan_with_live_owner_stays_refused(self):
        f = self.fixture
        self.orphan()
        before = f.ledger.read_bytes()
        with self.assertRaisesRegex(ValueError, 'owner or actor is still present'):
            self.recover()
        self.assertEqual(f.ledger.read_bytes(), before)
        self.assertTrue(f.marker.exists())

    def test_unadmitted_orphan_with_live_actor_stays_refused(self):
        f = self.fixture
        self.orphan()
        self.end_owner()
        f.process({'pid': 15, 'startticks': 105}, 12, ['compiler'],
                  str(f.group.relative_to(f.reader.root)))
        f.marker.write_text(f.marker.read_text().replace('confirmed\n', '15\n'))
        with self.assertRaisesRegex(ValueError, 'owner or actor is still present'):
            self.recover()
        self.assertTrue(f.marker.exists())

    def test_unadmitted_orphan_with_existing_scope_stays_refused(self):
        f = self.fixture
        self.orphan()
        self.end_owner()
        with self.assertRaisesRegex(ValueError, 'scope is still present'):
            self.recover()
        self.assertTrue(f.marker.exists())

    def test_authenticated_archive_recovery_preserves_the_release(self):
        import shell_archive
        f = self.fixture
        data = f.read()
        key = M.shell_key(f.marker)
        owner = data['shell_claim_owners'].pop(key)
        release = {'owner': owner['owner'], 'marker': owner['marker']}
        directory = f.root/'archive'
        digest = shell_archive.publish(directory, key,
                    {'shell_claim_owners': owner, 'shell_releases': release})
        data.update(shell_archive_directory=str(directory), shell_archive={key: digest})
        data['fixed_claims'][key] = 0
        f.save(data)
        self.end_owner()
        shutil.rmtree(f.group)
        self.assertTrue(self.recover())
        result = f.read()
        self.assertEqual(shell_archive.released_records(result, key, f.reader), (owner, release))
        self.assertEqual(result['shell_recovery_audits'][key]['route'], 'archived_release')

    def test_tampered_archive_cannot_authorize_recovery(self):
        import shell_archive
        f = self.fixture
        data = self.orphan()
        key = M.shell_key(f.marker)
        data.update(shell_archive_directory=str(f.root/'archive'), shell_archive={key: 'wrong'})
        (f.root/'archive').mkdir()
        shell_archive.document_path(f.root/'archive', key).write_text('{}')
        f.save(data)
        self.end_owner()
        shutil.rmtree(f.group)
        with self.assertRaisesRegex(ValueError, 'archive identity changed'):
            self.recover()
        self.assertTrue(f.marker.exists())

    def interrupt_confirmation(self):
        f = self.fixture
        data = f.read()
        data['shell_claim_owners'][M.shell_key(f.marker)].pop('token_identity')
        f.save(data)

    def test_missing_identity_confirmation_recovers_only_after_complete_absence(self):
        f = self.fixture
        self.interrupt_confirmation()
        self.end_owner()
        shutil.rmtree(f.group)
        self.assertTrue(self.recover())
        data = f.read()
        key = M.shell_key(f.marker)
        self.assertEqual(data['fixed_claims'][key], 0)
        self.assertEqual(data['shell_recovery_audits'][key]['route'], 'admitted_absence')
        self.assertTrue(M._shell_recovery_record(data, key, f.reader)[1]['absence_only'])

    def test_missing_identity_confirmation_with_live_owner_stays_refused(self):
        f = self.fixture
        self.interrupt_confirmation()
        before = f.ledger.read_bytes()
        with self.assertRaisesRegex(ValueError, 'owner or actor is still present'):
            self.recover()
        self.assertEqual(f.ledger.read_bytes(), before)
        self.assertTrue(f.marker.exists())

    def test_missing_leaf_publication_recovers_only_after_complete_absence(self):
        f = self.fixture
        self.end_owner()
        f.marker.write_text(f.marker.read_text().replace('confirmed\n', '99\n') + 'child_start=999\n')
        shutil.rmtree(f.group)
        self.assertTrue(self.recover())
        key = M.shell_key(f.marker)
        audit = f.read()['shell_recovery_audits'][key]
        self.assertEqual(audit['actor_pid'], 99)
        self.assertEqual(audit['route'], 'admitted_absence')

    def test_missing_leaf_publication_with_live_actor_stays_refused(self):
        f = self.fixture
        self.end_owner()
        f.process({'pid': 99, 'startticks': 999}, 12, ['compiler'],
                  str(f.group.relative_to(f.reader.root)))
        f.marker.write_text(f.marker.read_text().replace('confirmed\n', '99\n') + 'child_start=999\n')
        before = f.ledger.read_bytes()
        with self.assertRaisesRegex(ValueError, 'owner or actor is still present'):
            self.recover()
        self.assertEqual(f.ledger.read_bytes(), before)
        self.assertTrue(f.marker.exists())


    def drop_aggregate(self):
        f = self.fixture
        data = f.read()
        record = data['shell_claim_owners'][M.shell_key(f.marker)]
        record['aggregate'] = None
        record.pop('leaf', None)
        f.save(data)

    def test_confirmed_token_without_aggregate_releases_after_complete_absence(self):
        f = self.fixture
        self.drop_aggregate()
        self.end_owner()
        shutil.rmtree(f.group)
        self.assertTrue(self.recover())
        data = f.read()
        key = M.shell_key(f.marker)
        self.assertFalse(f.marker.exists())
        self.assertEqual(data['fixed_claims'][key], 0)
        audit = data['shell_recovery_audits'][key]
        self.assertEqual(audit['route'], 'admitted_absence')
        self.assertIn(f.group.name, audit['absent_scope_names'])
        self.assertTrue(M._shell_recovery_record(data, key, f.reader)[1]['absence_only'])

    def test_confirmed_token_without_aggregate_and_live_owner_stays_refused(self):
        f = self.fixture
        self.drop_aggregate()
        shutil.rmtree(f.group)
        before = f.ledger.read_bytes()
        with self.assertRaisesRegex(ValueError, 'owner or actor is still present'):
            self.recover()
        self.assertEqual(f.ledger.read_bytes(), before)
        self.assertTrue(f.marker.exists())

    def test_confirmed_token_without_aggregate_and_existing_unit_stays_refused(self):
        f = self.fixture
        self.drop_aggregate()
        self.end_owner()
        before = f.ledger.read_bytes()
        with self.assertRaisesRegex(ValueError, 'scope is still present'):
            self.recover()
        self.assertEqual(f.ledger.read_bytes(), before)
        self.assertTrue(f.marker.exists())

    def archive_stale_release(self):
        """Archive a stale-owner release that observed a later token."""
        import shell_archive
        f = self.fixture
        data = f.read()
        key = M.shell_key(f.marker)
        owner = data['shell_claim_owners'].pop(key)
        owner['aggregate'] = None
        f.marker.write_text(f.marker.read_text().replace('confirmed\n', '99\n') + 'child_start=999\n')
        release = {'owner': owner['owner'], 'marker': owner['marker'],
                   'stale_owner_recovery': True, 'released_bytes': 64 * M.GIB,
                   'previous_token_identity': owner['token_identity'],
                   'observed_token_identity': list(f.reader.file_identity(f.marker.lstat()))}
        directory = f.root/'archive'
        digest = shell_archive.publish(directory, key,
                    {'shell_claim_owners': owner, 'shell_releases': release})
        data.update(shell_archive_directory=str(directory), shell_archive={key: digest})
        data['fixed_claims'][key] = 0
        f.save(data)
        return key

    def test_zero_byte_archived_token_with_observed_identity_is_removed(self):
        f = self.fixture
        key = self.archive_stale_release()
        self.end_owner()
        shutil.rmtree(f.group)
        self.assertTrue(self.recover())
        data = f.read()
        self.assertFalse(f.marker.exists())
        self.assertEqual(data['fixed_claims'][key], 0)
        self.assertEqual(data['shell_recovery_audits'][key]['route'], 'archived_release')

    def test_zero_byte_archived_token_with_other_identity_stays_refused(self):
        f = self.fixture
        self.archive_stale_release()
        self.end_owner()
        shutil.rmtree(f.group)
        f.marker.write_text(f.marker.read_text() + 'changed=yes\n')
        with self.assertRaisesRegex(ValueError, 'archived released token identity changed'):
            self.recover()
        self.assertTrue(f.marker.exists())


if __name__ == '__main__':
    unittest.main()
