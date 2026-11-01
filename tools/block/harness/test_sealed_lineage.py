"""Test sealed lineage with nonproof supplier data and an isolated ledger."""
from copy import deepcopy
import json
import os
from pathlib import Path
import stat
import shutil
import unittest
from unittest.mock import patch

import sealed_lineage as seal
import test_supplier_ready as fixtures


class SealedLineage(unittest.TestCase):
    def setUp(self):
        self.fixture = fixtures.SupplierReady('runTest')
        self.fixture.setUp()
        self.addCleanup(self.fixture.doCleanups)
        self.root = self.fixture.root
        self.output = self.root / 'durable'
        self.harness = {
            'schema': 'block.shared-harness.git.v2',
            'root': '/home/cody/zesislar/.worktrees/shared-block-65ab9a73371b0d83ecf6f87967115340ed714172',
            'commit': '65ab9a73371b0d83ecf6f87967115340ed714172',
            'tree': '159e845f333975a50b42122f9c4387a809e1ea92',
            'tools_tree': '179d6596218a2b25825d338b50e8c723aa819f12'}
        self.fixture.ready['harness'] = self.harness
        self.fixture.ready['jobs'][0]['key'] = 'prerequisites'
        self.fixture.inner['harness'] = self.harness
        self.fixture.manifest['runtime'] = self.fixture.save('jobs/prerequisites/RUNTIME.json', self.fixture.inner)
        self.fixture.ready['bindings'].append(self.fixture.compiler['compiler'])
        self.history = self.fixture.file('past.json', json.dumps({'fixture': 'past data'}).encode())
        self.fixture.ready['bindings'].append(self.history)
        self.owner = {'token': 'fixture', 'pid': 1000000000, 'startticks': 1}
        closed = json.loads(Path(self.fixture.manifest['closure']['path']).read_text())
        closed.update(owner=self.owner, actors=[dict(ended=True, pid=1000000000, startticks=1)])
        self.fixture.manifest['closure'] = self.fixture.save('jobs/prerequisites/CLOSURE.json', closed)
        self.ledger = self.root / 'LEDGER.json'
        self.lock = self.root / 'LEDGER.lock'
        self.lock.touch()
        self.ledger_value = {'fixed_claims': {'supplier': 0}, 'entry_pilot_outside_releases': {
            'supplier': {'bytes': 24 * 1024**3, 'owner': self.owner,
                         'closure': self.fixture.manifest['closure']}}}
        self.save_ledger()
        for name, value in [('LEDGER', self.ledger), ('LOCK', self.lock)]:
            selected = patch.object(seal, name, value)
            selected.start()
            self.addCleanup(selected.stop)
        environment = patch.dict(os.environ, {'CAML_LD_LIBRARY_PATH': '', 'COQPATH': '', 'OCAMLPATH': ''})
        environment.start()
        self.addCleanup(environment.stop)

    def save_ledger(self):
        self.ledger.write_text(json.dumps(self.ledger_value))

    def publish(self):
        self.fixture.manifest['ready'] = self.fixture.save('READY-RUNTIME.json', self.fixture.ready)
        return seal.publish(self.fixture.freeze(), self.output)

    def test_publish_validates_and_keeps_original_payloads(self):
        before = deepcopy(self.fixture.ready)
        reference = self.publish()
        sealed = seal.validate(reference)
        self.assertEqual(self.fixture.ready, before)
        self.assertEqual(sealed['receipt']['producer_harness'], self.harness)
        self.assertEqual(sealed['receipt']['canonical_release']['bytes'], 24 * 1024**3)
        for name, row in sealed['receipt']['producer_originals'].items():
            self.assertEqual(Path(row['path']).read_bytes(),
                             Path(sealed['receipt']['producer_evidence'][name]['path']).read_bytes())
        self.assertEqual(stat.S_IMODE(Path(reference['path']).stat().st_mode), 0o400)

    def test_export_has_identical_bytes_and_distinct_inodes(self):
        reference = self.publish()
        rows = seal.verify_exports(reference)
        self.assertTrue(rows)
        for row in rows:
            path = Path(row['path'])
            original = self.fixture.workspace / path.relative_to(self.output / 'bank')
            self.assertEqual(original.read_bytes(), path.read_bytes())
            self.assertNotEqual(original.stat().st_ino, path.stat().st_ino)

    def test_historical_file_can_disappear_after_sealing(self):
        reference = self.publish()
        Path(self.history['path']).unlink()
        self.assertEqual(seal.validate(reference)['receipt']['historical_row_count'],
                         len(self.fixture.ready['bindings']))
        proposal = seal.project(self.fixture.ready, reference)
        self.assertIn(self.history, proposal['encapsulated_rows'])
        self.assertEqual(self.fixture.ready['bindings'][-1], self.history)

    def test_current_sources_and_compiler_remain_retained(self):
        reference = self.publish()
        proposal = seal.project(self.fixture.ready, reference)
        self.assertIn(self.fixture.compiler['compiler'], proposal['retained_rows'])
        for row in self.fixture.modules:
            self.assertIn(row['source'], proposal['retained_rows'])
            self.assertIn(row['object'], proposal['retained_rows'])
        self.assertTrue(proposal['current_direct_hashes'])

    def test_current_file_without_dependency_extension_is_hashed(self):
        path = self.fixture.workspace / 'Library/metadata.txt'
        path.write_text('fixture metadata')
        reference = self.publish()
        path.write_text('changed metadata')
        with self.assertRaisesRegex(ValueError, 'current compiler input'):
            seal.project(self.fixture.ready, reference)

    def test_current_mapped_source_outside_load_root_refuses_mutation(self):
        reference = self.publish()
        Path(self.fixture.modules[0]['source']['path']).write_text('changed source')
        with self.assertRaisesRegex(ValueError, 'current compiler input'):
            seal.project(self.fixture.ready, reference)

    def test_current_compiler_refuses_mutation(self):
        reference = self.publish()
        Path(self.fixture.compiler['compiler']['path']).write_bytes(b'changed compiler')
        with self.assertRaisesRegex(ValueError, 'current compiler input'):
            seal.project(self.fixture.ready, reference)

    def test_added_current_plugin_refuses(self):
        reference = self.publish()
        (self.fixture.workspace / 'Library/new.cmxs').write_bytes(b'new plugin')
        with self.assertRaisesRegex(ValueError, 'current compiler input'):
            seal.project(self.fixture.ready, reference)

    def test_current_metadata_preserves_transitive_old_input(self):
        target = self.fixture.file('named-input.v', b'fixture source')
        config = self.fixture.save('current-config.json', {'source_file': target['path']})
        self.fixture.ready['bindings'].extend([target, config])
        self.fixture.ready['current_config'] = config
        reference = self.publish()
        proposal = seal.project(self.fixture.ready, reference)
        self.assertIn(target, proposal['retained_rows'])
        self.assertIn(config, proposal['retained_rows'])

    def test_unknown_current_json_keeps_legacy_validation(self):
        config = self.fixture.save('unknown.json', {'fixture': True})
        self.fixture.ready['unknown_current_file'] = config['path']
        reference = self.publish()
        with self.assertRaisesRegex(ValueError, 'legacy validation'):
            seal.project(self.fixture.ready, reference)

    def test_failed_verification_cannot_seal(self):
        checks = json.loads(Path(self.fixture.manifest['verification']['path']).read_text())
        checks[0]['result']['success'] = False
        self.fixture.manifest['verification'] = self.fixture.save(
            'jobs/prerequisites/native/CONTROL-VERIFICATION.json', checks)
        with self.assertRaises(ValueError):
            self.publish()
        self.assertFalse((self.output / 'RECEIPT.json').exists())

    def test_live_actor_cannot_seal(self):
        closed = json.loads(Path(self.fixture.manifest['closure']['path']).read_text())
        fields = Path('/proc/self/stat').read_text().rsplit(')', 1)[1].split()
        closed['actors'] = [dict(ended=True, pid=os.getpid(), startticks=int(fields[19]))]
        self.fixture.manifest['closure'] = self.fixture.save('jobs/prerequisites/CLOSURE.json', closed)
        self.ledger_value['entry_pilot_outside_releases']['supplier']['closure'] = self.fixture.manifest['closure']
        self.save_ledger()
        with self.assertRaisesRegex(ValueError, 'actor'):
            self.publish()

    def test_positive_canonical_claim_cannot_seal(self):
        self.ledger_value['fixed_claims']['supplier'] = 24 * 1024**3
        self.save_ledger()
        with self.assertRaisesRegex(ValueError, 'live or unknown'):
            self.publish()

    def test_unknown_canonical_claim_cannot_seal(self):
        del self.ledger_value['fixed_claims']['supplier']
        self.save_ledger()
        with self.assertRaisesRegex(ValueError, 'live or unknown'):
            self.publish()

    def test_wrong_release_owner_cannot_seal(self):
        self.ledger_value['entry_pilot_outside_releases']['supplier']['owner'] = dict(self.owner, token='wrong')
        self.save_ledger()
        with self.assertRaisesRegex(ValueError, 'another producer'):
            self.publish()

    def test_wrong_release_amount_cannot_seal(self):
        self.ledger_value['entry_pilot_outside_releases']['supplier']['bytes'] = 1
        self.save_ledger()
        with self.assertRaisesRegex(ValueError, 'another producer'):
            self.publish()

    def test_wrong_execution_pin_cannot_seal(self):
        self.fixture.inner['harness'] = dict(self.harness, commit='0' * 40)
        self.fixture.manifest['runtime'] = self.fixture.save('jobs/prerequisites/RUNTIME.json', self.fixture.inner)
        with self.assertRaisesRegex(ValueError, 'producer tool pin'):
            self.publish()

    def test_changed_receipt_refuses(self):
        reference = self.publish()
        path = Path(reference['path'])
        path.chmod(0o600)
        path.write_text('{}')
        path.chmod(0o400)
        with self.assertRaisesRegex(ValueError, 'hash differs'):
            seal.validate(reference)

    def test_writable_receipt_refuses(self):
        reference = self.publish()
        Path(reference['path']).chmod(0o600)
        with self.assertRaisesRegex(ValueError, 'protected owned'):
            seal.validate(reference)

    def test_receipt_symlink_refuses(self):
        reference = self.publish()
        alias = self.root / 'alias.json'
        alias.symlink_to(reference['path'])
        with self.assertRaisesRegex(ValueError, 'protected owned'):
            seal.validate(dict(reference, path=str(alias)))

    def test_changed_durable_evidence_refuses(self):
        reference = self.publish()
        path = self.output / 'evidence/calls.json'
        path.chmod(0o600)
        path.write_text('[]')
        path.chmod(0o400)
        with self.assertRaisesRegex(ValueError, 'hash differs'):
            seal.validate(reference)

    def test_changed_export_refuses_adoption(self):
        reference = self.publish()
        path = self.output / 'bank/Library/Dependency.vo'
        path.write_bytes(b'changed object')
        with self.assertRaisesRegex(ValueError, 'hash differs'):
            seal.verify_exports(reference)

    def test_added_export_refuses_adoption(self):
        reference = self.publish()
        (self.output / 'bank/extra.cmxs').write_bytes(b'new plugin')
        with self.assertRaisesRegex(ValueError, 'inventory changed'):
            seal.verify_exports(reference)

    def test_changed_current_object_refuses(self):
        reference = self.publish()
        Path(self.fixture.modules[0]['object']['path']).write_bytes(b'changed object')
        with self.assertRaisesRegex(ValueError, 'current compiler input'):
            seal.project(self.fixture.ready, reference)

    def test_changed_flags_preserve_legacy_path(self):
        reference = self.publish()
        current = deepcopy(self.fixture.ready)
        current['physical_flags'] = current['physical_flags'] + ['-w', '-all']
        with self.assertRaisesRegex(ValueError, 'flag context'):
            seal.project(current, reference)

    def test_wrong_canonical_closure_refuses(self):
        self.ledger_value['entry_pilot_outside_releases']['supplier']['closure'] = {
            'path': '/wrong/closure', 'sha256': '0' * 64}
        self.save_ledger()
        with self.assertRaisesRegex(ValueError, 'another producer'):
            self.publish()

    def test_receipt_survives_producer_workspace_and_evidence_removal(self):
        reference = self.publish()
        shutil.rmtree(self.fixture.workspace)
        shutil.rmtree(self.root / 'jobs')
        for name in ['READY-RUNTIME.json', 'SUPPLIER.json', 'SOURCE.json', 'GRAPH.json', 'RESULT.json']:
            (self.root / name).unlink()
        self.assertEqual(seal.validate(reference)['receipt']['producer_harness'], self.harness)
        self.assertTrue(seal.verify_exports(reference))

    def test_export_verification_refuses_a_hashing_race(self):
        reference = self.publish()
        original = seal.binding
        changed = False

        def racing(path):
            nonlocal changed
            result = original(path)
            if not changed and Path(path).is_relative_to(self.output / 'bank'):
                changed = True
                Path(path).write_bytes(b'mutated after hashing')
            return result

        with patch.object(seal, 'binding', side_effect=racing):
            with self.assertRaisesRegex(ValueError, 'changed during verification'):
                seal.verify_exports(reference)

    def test_current_input_collection_refuses_a_hashing_race(self):
        reference = self.publish()
        original = seal.binding
        changed = False

        def racing(path):
            nonlocal changed
            result = original(path)
            if not changed and Path(path) == Path(self.fixture.compiler['compiler']['path']):
                changed = True
                Path(path).write_bytes(b'mutated after hashing')
            return result

        with patch.object(seal, 'binding', side_effect=racing):
            with self.assertRaisesRegex(ValueError, 'namespace changed'):
                seal.project(self.fixture.ready, reference)

    def test_full_checks_run_at_both_publication_boundaries(self):
        import proof_bindings
        import supplier_ready
        from binding_cache import _FORCE
        full, supplier = proof_bindings.check_proof_bindings, supplier_ready.validate
        full_checks, supplier_checks = [], []

        def checked_full(runtime, force_full=False):
            full_checks.append((_FORCE.get(), force_full))
            return full(runtime, force_full=force_full)

        def checked_supplier(reference):
            supplier_checks.append(_FORCE.get())
            return supplier(reference)

        with patch.object(proof_bindings, 'check_proof_bindings', side_effect=checked_full), \
                patch.object(supplier_ready, 'validate', side_effect=checked_supplier):
            self.publish()
        self.assertEqual(full_checks, [(True, True), (True, True)])
        self.assertEqual(supplier_checks, [True, True])

    def test_relative_context_directory_change_preserves_legacy_path(self):
        self.fixture.flags[:] = ['-Q', 'Library', 'Library']
        self.fixture.manifest['runtime'] = self.fixture.save(
            'jobs/prerequisites/RUNTIME.json', self.fixture.inner)
        original = os.getcwd()
        try:
            os.chdir(self.fixture.workspace)
            reference = self.publish()
            os.chdir(self.root)
            with self.assertRaisesRegex(ValueError, 'relative compiler context'):
                seal.project(self.fixture.ready, reference)
        finally:
            os.chdir(original)

    def test_export_alias_escape_refuses_publication(self):
        (self.fixture.workspace / 'external').symlink_to(self.root)
        with self.assertRaisesRegex(ValueError, 'alias cannot be exported'):
            self.publish()

    def test_existing_output_is_not_replaced(self):
        self.output.mkdir()
        marker = self.output / 'unchanged'
        marker.write_bytes(b'original')
        with self.assertRaisesRegex(ValueError, 'already exists'):
            self.publish()
        self.assertEqual(marker.read_bytes(), b'original')


if __name__ == '__main__':
    unittest.main()
