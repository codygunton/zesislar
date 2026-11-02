"""Migration keeps accepted origins and complete Rocq dependency comparisons."""
import copy
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

import scratch
from entry_chain import binding
import object_import_migration as migration
from object_imports import compatibility
REAL_INSPECTOR = migration.inspector


class MigrationTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.workspace = self.root / 'bank'
        self.workspace.mkdir()
        self.source = self.workspace / 'ReturnBundle.v'
        self.source.write_text('(* Accepted source fixture. *)\n')
        self.obj = self.source.with_suffix('.vo')
        self.obj.write_bytes(b'accepted owner')
        self.dependency = self.workspace / 'PureFacts.vo'
        self.dependency.write_bytes(b'accepted dependency')
        self.installed = self.root / 'Installed.vo'
        self.installed.write_bytes(b'installed dependency')
        (self.root / 'coqc').write_bytes(b'compiler')
        (self.root / 'coqdep').write_bytes(b'resolver')
        self.compiler = binding(self.root / 'coqc')
        self.coqdep = binding(self.root / 'coqdep')
        self.flags = ['-R', str(self.workspace), 'ZesuSsz']
        self.module = 'ZesuSsz.ReturnBundle'
        self.names = ['Coq.Installed', 'ZesuSsz.PureFacts']
        self.paths = dict(zip(self.names, [self.installed, self.dependency]))
        self.ready = self.save('READY.json', {'prepared_workspace': str(self.workspace),
            'physical_flags': self.flags, 'bindings': [self.compiler, self.coqdep]})
        self.supplier = self.save('SUPPLIER.json', {'ready': self.ready, 'modules': [{
            'module': self.module, 'source': binding(self.source), 'object': binding(self.obj)}]})
        self.policy = {'origins': [{'kind': 'accepted-supplier', 'binding': self.supplier,
            'ready': self.ready}], 'inspector_build': {'path': 'pinned', 'sha256': 'approved'}}
        policy = self.root / 'POLICY.json'
        policy.write_text(json.dumps(self.policy))
        self.addCleanup(patch.stopall)
        patch.object(migration, 'POLICY', policy).start()
        patch.object(migration, 'inspector', side_effect=self.inspect).start()
        resolver = patch.object(migration, 'InstalledMappings').start()
        resolver.return_value.resolution.side_effect = lambda name: {
            'canonical': name, 'object': self.paths[name]}

    def save(self, name, data):
        path = self.root / name
        path.write_text(json.dumps(data))
        return binding(path)

    def inspect(self, policy, objects, checks):
        return {'objects': [{'path': str(self.obj), 'module': self.module,
                'imports': [{'module': name} for name in self.names]}],
            'checks': [{**row, 'compatible': True} for row in checks]}

    def create(self):
        return migration.create(self.supplier, self.module, self.source, self.obj,
                                self.compiler, self.flags, self.workspace)

    def validate(self, receipt):
        return migration.validate(self.save('MIGRATION.json', receipt), self.module,
            self.source, self.obj, self.compiler, self.flags, self.workspace)

    def test_matching_supplier_origin_keeps_label_and_checks_installed(self):
        receipt = self.create()
        self.assertEqual(receipt['origin']['kind'], 'inherited-from-accepted-supplier')
        self.assertEqual(len(receipt['comparison']['checks']), 2)
        imports, workspace = self.validate(receipt)
        self.assertEqual(set(imports), {'ZesuSsz.PureFacts'})
        self.assertEqual(workspace, self.workspace)
        self.assertNotIn('successful_compilation', receipt)

    def test_batch_does_not_retain_parsed_migration_receipt(self):
        receipt = self.create()
        reference = self.save('MIGRATION.json', receipt)
        with migration.batch() as active:
            migration.validate(reference, self.module, self.source, self.obj,
                               self.compiler, self.flags, self.workspace)
            self.assertFalse(any(key[0] == reference['path'] for key in active['records']))
            self.assertTrue(active['records'])  # Shared origin inputs remain cached.

    def test_changed_PureFacts_refuses_ReturnBundle(self):
        receipt = self.create()
        self.dependency.write_bytes(b'changed dependency')
        with self.assertRaisesRegex(ValueError, 'resolved current bank'):
            self.validate(receipt)

    def test_changed_installed_dependency_refuses(self):
        receipt = self.create()
        self.installed.write_bytes(b'changed installed library')
        with self.assertRaisesRegex(ValueError, 'resolved current bank'):
            self.validate(receipt)

    def test_missing_recorded_import_refuses(self):
        receipt = self.create()
        receipt['imported_objects'].pop()
        with self.assertRaisesRegex(ValueError, 'resolved current bank'):
            self.validate(receipt)

    def test_extra_recorded_import_refuses(self):
        receipt = self.create()
        receipt['imported_objects'].append({'module': 'Coq.Extra', 'object': binding(self.installed)})
        with self.assertRaisesRegex(ValueError, 'resolved current bank'):
            self.validate(receipt)

    def test_successful_subset_refuses(self):
        receipt = self.create()
        receipt['comparison']['checks'].pop()
        with self.assertRaisesRegex(ValueError, 'complete successful comparisons'):
            self.validate(receipt)

    def test_real_inspector_refusal_overrides_forged_success(self):
        receipt = self.create()
        def refuse(policy, objects, checks):
            result = self.inspect(policy, objects, checks)
            for row in result['checks']:
                row['compatible'] = False
            return result
        with patch.object(migration, 'inspector', side_effect=refuse):
            with self.assertRaisesRegex(ValueError, 'digest comparison refused'):
                self.validate(receipt)

    def test_unapproved_origin_refuses(self):
        reference = dict(self.supplier, sha256='unknown')
        with self.assertRaisesRegex(ValueError, 'not an approved publication'):
            migration.create(reference, self.module, self.source, self.obj,
                             self.compiler, self.flags, self.workspace)

    def test_changed_source_or_object_refuses(self):
        for path in [self.source, self.obj]:
            previous = path.read_bytes()
            path.write_bytes(b'changed')
            with self.assertRaisesRegex(ValueError, 'accepted origin inputs'):
                self.create()
            path.write_bytes(previous)

    def test_changed_flags_refuse(self):
        with self.assertRaisesRegex(ValueError, 'accepted origin inputs'):
            migration.create(self.supplier, self.module, self.source, self.obj,
                self.compiler, self.flags + ['-w', 'all'], self.workspace)

    def test_origin_label_cannot_claim_compilation(self):
        receipt = self.create()
        receipt['origin']['kind'] = 'individual-accepted-compilation'
        with self.assertRaisesRegex(ValueError, 'authenticated receipt'):
            self.validate(receipt)

    def test_scheduled_dependency_still_refuses(self):
        receipt = self.save('MIGRATION.json', self.create())
        (self.workspace / 'PureFacts.v').write_text('(* Dependency. *)\n')
        result = compatibility([self.module], [
            {'from': self.module, 'to': 'ZesuSsz.PureFacts'}],
            {self.module: 'ReturnBundle.v', 'ZesuSsz.PureFacts': 'PureFacts.v'},
            self.workspace, {self.module: receipt}, self.compiler, self.flags,
            planned=['ZesuSsz.PureFacts'])
        self.assertIn('scheduled source compilation', result['rebuild'][0]['reason'])

    def test_public_manifest_preserves_existing_receipts(self):
        reference=self.save('MIGRATION.json',self.create())
        manifest=self.save('MANIFEST.json',{'schema':'entry-chain.object-import-migrations.v1',
            'receipts':{self.module:reference}})
        config={'proof_runtime':{'module_files':{self.module:'ReturnBundle.v'}},
            'object_imports':{'Coq.Previous':{'path':'original','sha256':'unchanged'}},'bindings':[]}
        scratch.install_object_import_migrations(config,Path(manifest['path']))
        self.assertEqual(config['object_imports'][self.module],reference)
        self.assertEqual(config['object_imports']['Coq.Previous']['path'],'original')
        self.assertIn(manifest,config['bindings'])
        self.assertIn(reference,config['bindings'])

    def test_public_manifest_refuses_another_module(self):
        receipt=self.create()
        reference=self.save('MIGRATION.json',receipt)
        manifest=self.save('MANIFEST.json',{'schema':'entry-chain.object-import-migrations.v1',
            'receipts':{'ZesuSsz.Other':reference}})
        config={'proof_runtime':{'module_files':{'ZesuSsz.Other':'Other.v'}},'bindings':[]}
        with self.assertRaisesRegex(ValueError,'another module or schema'):
            scratch.install_object_import_migrations(config,Path(manifest['path']))

    def test_index_alias_uses_the_inspected_object_identity(self):
        resolver=migration.InstalledMappings.return_value
        resolver.resolution.side_effect=lambda name: {
            'canonical':'IndexAlias.'+name,'object':self.paths[name]}
        receipt=self.create()
        self.assertEqual(len(receipt['comparison']['resolver_aliases']),2)
        self.validate(receipt)

    def test_inspector_identity_mismatch_still_refuses(self):
        def wrong(policy,objects,checks):
            if checks:
                raise ValueError('A resolved Coq object has another module name.')
            return self.inspect(policy,objects,checks)
        with patch.object(migration,'inspector',side_effect=wrong):
            with self.assertRaisesRegex(ValueError,'another module name'):
                self.create()

    def test_accepted_READY_requires_the_exact_selected_object(self):
        ready=self.save('SELECTED-READY.json',{
            'prepared_workspace':str(self.workspace),'physical_flags':self.flags,
            'bindings':[self.compiler,self.coqdep,binding(self.source),binding(self.obj)],
            'proof_runtime':{'module_files':{self.module:'ReturnBundle.v'}}})
        selection=self.save('SELECTION.json',{'rows':[ready],
            'recorded_expected_objects':{self.module:binding(self.obj)['sha256']}})
        authority={'kind':'accepted-ready','binding':ready,'ready':ready,
            'selection':selection,'selection_guards':{self.module:binding(self.obj)['sha256']}}
        self.policy['origins'].append(authority)
        migration.POLICY.write_text(json.dumps(self.policy))
        receipt=migration.create(ready,self.module,self.source,self.obj,
            self.compiler,self.flags,self.workspace)
        self.assertEqual(receipt['origin']['kind'],'inherited-from-accepted-READY')
        self.validate(receipt)
        authority['selection_guards'][self.module]='altered'
        migration.POLICY.write_text(json.dumps(self.policy))
        with self.assertRaisesRegex(ValueError,'exact authorized selection'):
            self.validate(receipt)

    def test_selected_READY_allows_other_exact_bound_owned_modules(self):
        marker_module, marker_source, marker_object=self.module,self.source,self.obj
        self.module='ZesuSsz.Extra'
        self.source=self.workspace/'Extra.v'
        self.source.write_text('(* Another accepted owned source. *)\n')
        self.obj=self.source.with_suffix('.vo')
        self.obj.write_bytes(b'another owned object')
        data={'prepared_workspace':str(self.workspace),'physical_flags':self.flags,
            'bindings':[self.compiler,self.coqdep,binding(marker_source),binding(marker_object),
                        binding(self.source),binding(self.obj)],
            'proof_runtime':{'module_files':{marker_module:'ReturnBundle.v',self.module:'Extra.v'}}}
        ready=self.save('SELECTED-READY.json',data)
        guards={marker_module:binding(marker_object)['sha256']}
        selection=self.save('SELECTION.json',{'rows':[ready],'recorded_expected_objects':guards})
        authority={'kind':'accepted-ready','binding':ready,'ready':ready,
            'selection':selection,'selection_guards':guards}
        self.policy['origins'].append(authority)
        migration.POLICY.write_text(json.dumps(self.policy))
        receipt=migration.create(ready,self.module,self.source,self.obj,
            self.compiler,self.flags,self.workspace)
        self.validate(receipt)
        authority['module_allowlist']=[marker_module]
        migration.POLICY.write_text(json.dumps(self.policy))
        with self.assertRaisesRegex(ValueError,'does not authorize this module origin'):
            migration.create(ready,self.module,self.source,self.obj,
                self.compiler,self.flags,self.workspace)
        authority['module_allowlist']=[self.module]
        data['bindings'].remove(binding(self.obj))
        changed=self.save('UNBOUND-READY.json',data)
        selection=self.save('UNBOUND-SELECTION.json',{'rows':[changed],'recorded_expected_objects':guards})
        authority.update(binding=changed,ready=changed,selection=selection)
        migration.POLICY.write_text(json.dumps(self.policy))
        with self.assertRaisesRegex(ValueError,'lacks bound source/object identities'):
            migration.create(changed,self.module,self.source,self.obj,
                self.compiler,self.flags,self.workspace)

    def test_batch_cache_rechecks_file_identities_and_separates_flags(self):
        calls=[]
        def run(policy,paths,checks):
            calls.append((list(paths),list(checks)))
            return {'objects':[{'path':str(path),'module':str(path),'imports':[]} for path in paths],
                'checks':[{**row,'compatible':True} for row in checks]}
        policy={'inspector_build':{'sha256':'approved'}}
        with patch.object(migration,'inspector_spec',return_value={'sha256':'pinned'}), \
                patch.object(migration,'run_inspector',side_effect=run), migration.batch() as state:
            state['context']=('flags-a','compiler-a')
            check={'owner':str(self.obj),'module':'ZesuSsz.PureFacts','object':str(self.dependency)}
            REAL_INSPECTOR(policy,[self.obj,self.dependency],[check])
            REAL_INSPECTOR(policy,[self.obj,self.dependency],[check])
            self.assertEqual(len(calls),1)
            self.dependency.write_bytes(b'changed')
            REAL_INSPECTOR(policy,[self.obj,self.dependency],[check])
            self.assertEqual(len(calls),2)
            state['context']=('flags-b','compiler-a')
            REAL_INSPECTOR(policy,[self.obj,self.dependency],[check])
            self.assertEqual(len(calls),3)


if __name__ == '__main__':
    unittest.main()
