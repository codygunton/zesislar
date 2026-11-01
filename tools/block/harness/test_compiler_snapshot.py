"""Exercise sealed validation with nonproof files and no compiler execution."""
import json
import os
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

import scratch
import compiler_snapshot as S
from entry_chain import binding, save
from proof_bindings import check_proof_bindings, proof_rows


class CompilerSnapshotTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.source = self.root / 'Control.v'
        self.source.write_text('nonproof test data\n')
        self.compiler = self.root / 'switch/bin/coqc'
        self.compiler.parent.mkdir(parents=True)
        self.compiler.write_text('nonexecutable compiler fixture\n')
        self.library = self.root / 'library'
        self.library.mkdir()
        self.obj = self.library / 'Dependency.vo'
        self.obj.write_text('nonproof object fixture\n')
        self.path = self.root / 'RUNTIME.json'
        self.source_binding=binding(self.source)
        self.runtime = {'physical_compiler':binding(self.compiler),'bindings': [binding(self.source), binding(self.obj), binding(self.compiler)],
                        'physical_flags': ['-Q', str(self.library), 'Example']}
        self.snapshot_path = self.root / 'SNAPSHOT.json'

    def seal(self, validate=None):
        save(self.path, self.runtime)
        self.reference = binding(self.path)
        self.runtime.update(runtime_path=str(self.path), runtime_sha256=self.reference['sha256'])
        return S.publish(self.runtime, validate or
                         (lambda: check_proof_bindings(self.runtime, force_full=True)), self.snapshot_path,compiler=self.compiler,environment={})

    def read(self, reference):
        return S.read(reference, self.reference)

    def test_round_trip_preserves_all_classified_rows(self):
        reference = self.seal()
        self.assertEqual(self.snapshot_path.stat().st_mode & 0o777, 0o600)
        self.assertEqual([r['path'] for r in self.read(reference)['rows']],
                         [str(self.source), str(self.obj), str(self.compiler), str(self.path)])

    def test_external_inventory_preserves_rows_and_exact_validation(self):
        original = self.runtime['bindings'][:]
        S.externalize(self.runtime, self.root / 'ROWS.json')
        self.assertNotIn('bindings', self.runtime)
        self.assertEqual(S.binding_rows(self.runtime), original)
        self.assertEqual(proof_rows(self.runtime), original)
        reference = self.seal()
        self.assertEqual(len(self.read(reference)['rows']), 5)
        self.obj.write_text('changed input')
        with self.assertRaises(ValueError):
            check_proof_bindings(self.runtime, force_full=True)

    def test_external_inventory_tamper_refuses(self):
        S.externalize(self.runtime, self.root / 'ROWS.json')
        (self.root / 'ROWS.json').write_text('{}')
        with self.assertRaises(ValueError):
            proof_rows(self.runtime)

    def test_duplicate_inventory_representation_refuses(self):
        S.externalize(self.runtime, self.root / 'ROWS.json')
        self.runtime['bindings'] = []
        with self.assertRaises(ValueError):
            S.binding_rows(self.runtime)

    def test_initial_validation_failure_publishes_nothing(self):
        def refuse():
            raise ValueError('initial refusal')
        with self.assertRaisesRegex(ValueError, 'initial refusal'):
            self.seal(refuse)
        self.assertFalse(self.snapshot_path.exists())

    def test_mutation_during_forced_validation_refuses(self):
        with self.assertRaisesRegex(ValueError, 'during full validation'):
            self.seal(lambda: self.obj.write_text('changed'))
        self.assertFalse(self.snapshot_path.exists())

    def test_seed_runtime_retains_original_full_validation(self):
        self.runtime['seed_binding_reference'] = {'test_data': True}
        calls = []
        self.assertIsNone(self.seal(lambda: calls.append('full')))
        self.assertEqual(calls, ['full'])
        self.assertFalse(self.snapshot_path.exists())

    def test_snapshot_tamper_refuses_hash(self):
        reference = self.seal()
        self.snapshot_path.write_text('{}')
        with self.assertRaisesRegex(ValueError, 'hash differs'):
            self.read(reference)

    def test_other_runtime_refuses(self):
        reference = self.seal()
        with self.assertRaisesRegex(ValueError, 'another runtime'):
            S.read(reference, dict(self.reference, sha256='0' * 64))

    def test_public_permissions_refuse(self):
        reference = self.seal()
        self.snapshot_path.chmod(0o644)
        with self.assertRaisesRegex(ValueError, 'private regular'):
            self.read(reference)

    def test_snapshot_symlink_refuses(self):
        reference = self.seal()
        alias = self.root / 'alias'
        alias.symlink_to(self.snapshot_path)
        with self.assertRaises(OSError):
            self.read(dict(reference, path=str(alias)))

    def test_snapshot_hardlink_refuses(self):
        reference = self.seal()
        os.link(self.snapshot_path, self.root / 'alias')
        with self.assertRaisesRegex(ValueError, 'private regular'):
            self.read(reference)

    def test_existing_snapshot_is_not_replaced(self):
        reference = self.seal()
        with self.assertRaises(FileExistsError):
            S.publish(self.runtime, lambda: check_proof_bindings(self.runtime, force_full=True), self.snapshot_path,compiler=self.compiler,environment={})
        self.assertEqual(binding(self.snapshot_path), reference)
        self.assertEqual(list(self.root.glob('.compiler-validation-*')), [])

    def test_content_change_with_restored_mtime_refuses(self):
        reference = self.seal()
        before = self.obj.stat()
        self.obj.write_bytes(b'x' * before.st_size)
        os.utime(self.obj, ns=(before.st_atime_ns, before.st_mtime_ns))
        with self.assertRaisesRegex(ValueError, 'identity changed'):
            self.read(reference)

    def test_atomic_replacement_refuses(self):
        reference = self.seal()
        replacement = self.root / 'replacement'
        replacement.write_bytes(self.obj.read_bytes())
        replacement.replace(self.obj)
        with self.assertRaisesRegex(ValueError, 'identity changed'):
            self.read(reference)

    def test_permission_change_refuses(self):
        reference = self.seal()
        self.obj.chmod(0o600)
        with self.assertRaisesRegex(ValueError, 'identity changed'):
            self.read(reference)

    def test_symlink_retarget_refuses(self):
        alias = self.root / 'input'
        alias.symlink_to(self.obj)
        self.runtime['bindings'][1]['path'] = str(alias)
        reference = self.seal()
        other = self.root / 'other'
        other.write_bytes(self.obj.read_bytes())
        alias.unlink()
        alias.symlink_to(other)
        with self.assertRaisesRegex(ValueError, 'identity changed'):
            self.read(reference)

    def test_parent_alias_retarget_refuses(self):
        alias = self.root / 'parent'
        alias.symlink_to(self.library, target_is_directory=True)
        self.runtime['bindings'][1]['path'] = str(alias / self.obj.name)
        reference = self.seal()
        other = self.root / 'other'
        other.mkdir()
        (other / self.obj.name).write_bytes(self.obj.read_bytes())
        alias.unlink()
        alias.symlink_to(other, target_is_directory=True)
        with self.assertRaisesRegex(ValueError, 'identity changed'):
            self.read(reference)

    def test_direct_inputs_force_hashing_and_include_dependency_superset(self):
        implicit = self.compiler.parent.parent / 'lib/coq-stdlib/theories/Implicit.vo'
        implicit.parent.mkdir(parents=True)
        implicit.write_text('implicit dependency fixture')
        with patch('binding_cache._persistent', side_effect=AssertionError('persistent access')):
            rows = S.hash_inputs(self.source, self.compiler, self.runtime['physical_flags'])
        self.assertEqual({row['path'] for row in rows},
                         {str(p) for p in [self.source, self.compiler, self.obj, implicit]})

    def test_compiler_does_not_reclassify_rows(self):
        reference = self.seal()
        with patch('proof_bindings.proof_rows', side_effect=AssertionError('reclassified')):
            report = S.validate_compiler(self.runtime, self.reference, reference, self.source_binding, self.compiler)
        self.assertEqual(report['retained_identities_checked'], 4)
        self.assertEqual(len(report['directly_hashed_inputs']), 3)

    def test_mutation_during_direct_hashing_refuses(self):
        reference = self.seal()
        def mutate(*args):
            self.obj.write_text('changed')
            return [dict(self.source_binding,identity=S._identity(self.source)),dict(binding(self.compiler),identity=S._identity(self.compiler))]
        with patch.object(S, 'hash_inputs', side_effect=mutate):
            with self.assertRaisesRegex(ValueError, 'during input hashing'):
                S.validate_compiler(self.runtime, self.reference, reference, self.source_binding, self.compiler)

    def accept_output(self,ledger,obj,source=None,before_accept=None):
        """Create labelled nonproof physical data. Invoke no compiler or admission."""
        source=source or self.source
        source_row=binding(source);compiler=binding(self.compiler)
        report={'snapshot':ledger.reference,'producer':ledger.snapshot['producer'],
                'accepted_dependency_identities':[]}
        for reference in ledger.rows:
            receipt=json.loads(Path(reference['path']).read_text())
            artifact=receipt['sidecar']
            report['accepted_dependency_identities']=[row for row in report['accepted_dependency_identities']
                if row['canonical_path']!=artifact['canonical_path']]
            report['accepted_dependency_identities'].append(dict(artifact['binding'],
                identity=artifact['identity'],namespace=artifact['namespace'],
                canonical_path=artifact['canonical_path'],source=receipt['source'],kind='vos',
                primary_object=receipt['object']['path'],receipt=reference))
        before=S.sidecar_prestate(source_row,obj,compiler,self.runtime['physical_flags'],report)
        sidecar=obj.with_suffix('.vos')
        if not sidecar.exists():sidecar.write_bytes(b'')
        directory=self.root/'compiler-invocations'/('%032x'%len(ledger.rows))
        directory.mkdir(parents=True)
        argv=[compiler['path'],*self.runtime['physical_flags'],source_row['path']]
        inputs=S._publish(directory/'INPUT.json',{'source':source_row,'compiler':compiler,
            'physical_argv':argv,'sidecar_prestate':before,
            'validation':{'runtime':ledger.snapshot['runtime'],'snapshot':ledger.reference}})
        physical=S._publish(directory/'PHYSICAL-RESULT.json',{'input':inputs,'physical_argv':argv,
            'returncode':0,'output_capture':{'complete':True},'output_validation':{'success':True},
            'compiler_outputs':S.compiler_outputs(obj,before),'fixture':'Nonproof test data.'})
        if before_accept is not None:before_accept(sidecar)
        return ledger.accept(source,obj,self.compiler,self.runtime['physical_flags'],{'success':True},physical_result=physical)

    def outputs(self):
        source=self.library/'Later.v'
        source.write_text('nonproof generated source fixture')
        self.source=source;self.source_binding=binding(source)
        self.runtime['bindings'].append(self.source_binding)
        reference = self.seal()
        snapshot = self.read(reference)
        ledger = S.OutputReceipts(snapshot, reference)
        obj = self.library / 'Later.vo'
        obj.write_text('object from a successful nonproof fixture')
        receipt = self.accept_output(ledger,obj)
        return reference, snapshot, ledger, obj, receipt

    def validate_outputs(self, reference, ledger):
        return S.validate_compiler(self.runtime, self.reference, reference,
            self.source_binding, self.compiler, output_key=ledger.key)

    def test_later_successful_object_has_validated_receipt(self):
        reference, snapshot, ledger, obj, receipt = self.outputs()
        report = self.validate_outputs(reference, ledger)
        self.assertEqual(report['accepted_dependency_objects'], [binding(obj)])
        self.assertEqual(Path(receipt['path']).stat().st_mode & 0o777, 0o600)
        self.assertNotIn(ledger.key, self.snapshot_path.read_text())
        self.assertNotIn(ledger.key, Path(receipt['path']).read_text())
        self.assertNotIn(ledger.key, (ledger.root / 'INDEX.json').read_text())

    def aliased_outputs(self):
        workspace=self.root/'workspace'
        self.library=workspace/'artifacts/default'
        self.library.mkdir(parents=True)
        self.alias=workspace/'default'
        self.alias.symlink_to('artifacts/default',target_is_directory=True)
        self.runtime['physical_flags']=['-Q',str(self.alias),'Example',
                                      '-Q',str(self.library),'Example']
        return self.outputs()

    def test_actual_default_layout_accepts_authenticated_object_identity(self):
        reference,snapshot,ledger,obj,receipt=self.aliased_outputs()
        report=self.validate_outputs(reference,ledger)
        inputs={row['path']:row for row in report['directly_hashed_inputs']}
        lexical=self.alias/obj.name
        self.assertIn(str(lexical),inputs)
        self.assertIn(str(obj),inputs)
        self.assertEqual(inputs[str(lexical)]['identity'][1],inputs[str(obj)]['identity'][1])
        accepted=json.loads(Path(receipt['path']).read_text())
        self.assertEqual(accepted['object_lexical_path'],str(obj))
        self.assertEqual(accepted['object_canonical_path'],str(obj.resolve()))
        self.assertEqual(accepted['object_identity'],S._identity(obj))
        self.assertEqual(report['accepted_dependency_objects'],[binding(obj)])

    def test_same_source_recompile_updates_only_authenticated_identity(self):
        reference,snapshot,ledger,obj,receipt=self.aliased_outputs()
        original=json.loads(Path(receipt['path']).read_text())['object_identity']
        obj.write_bytes(obj.read_bytes())
        second=self.accept_output(ledger,obj)
        self.assertNotEqual(original,json.loads(Path(second['path']).read_text())['object_identity'])
        self.assertEqual(len(self.validate_outputs(reference,ledger)['accepted_dependency_objects']),2)

    def test_produced_alias_retarget_refuses_even_for_same_target(self):
        reference,snapshot,ledger,obj,receipt=self.aliased_outputs()
        self.alias.unlink()
        self.alias.symlink_to('artifacts/./default',target_is_directory=True)
        with self.assertRaisesRegex(ValueError,'mapping namespace changed'):
            self.validate_outputs(reference,ledger)

    def test_produced_alias_retarget_to_other_object_refuses(self):
        reference,snapshot,ledger,obj,receipt=self.aliased_outputs()
        other=self.root/'other'
        other.mkdir();(other/obj.name).write_bytes(obj.read_bytes())
        self.alias.unlink();self.alias.symlink_to(other,target_is_directory=True)
        with self.assertRaisesRegex(ValueError,'mapping namespace changed'):
            self.validate_outputs(reference,ledger)

    def test_identical_byte_produced_object_replacement_refuses(self):
        reference,snapshot,ledger,obj,receipt=self.aliased_outputs()
        replacement=obj.with_suffix('.replacement')
        replacement.write_bytes(obj.read_bytes());replacement.replace(obj)
        with self.assertRaisesRegex(ValueError,'object identity changed'):
            self.validate_outputs(reference,ledger)

    def test_same_byte_write_with_restored_mtime_needs_new_receipt(self):
        reference,snapshot,ledger,obj,receipt=self.aliased_outputs()
        before=obj.stat();obj.write_bytes(obj.read_bytes())
        os.utime(obj,ns=(before.st_atime_ns,before.st_mtime_ns))
        with self.assertRaisesRegex(ValueError,'object identity changed'):
            self.validate_outputs(reference,ledger)

    def test_conflicting_source_receipts_for_same_object_refuse(self):
        reference,snapshot,ledger,obj,receipt=self.aliased_outputs()
        different=self.root/'Different.v'
        different.write_bytes(self.source.read_bytes())
        with self.assertRaisesRegex(ValueError,'preexisting compiler sidecar'):
            self.accept_output(ledger,obj,source=different)

    def test_legacy_object_receipt_cannot_invent_identity(self):
        publish=S._publish
        def legacy(path,value,**kwargs):
            if 'successful_compilation' in value:
                value={key:item for key,item in value.items() if not key.startswith('object_')}
            return publish(path,value,**kwargs)
        with patch.object(S,'_publish',side_effect=legacy):
            reference,snapshot,ledger,obj,receipt=self.aliased_outputs()
        with self.assertRaisesRegex(ValueError,'exact identity or namespace'):
            self.validate_outputs(reference,ledger)

    def test_produced_object_race_after_direct_hashing_refuses(self):
        reference,snapshot,ledger,obj,receipt=self.aliased_outputs()
        hash_inputs=S.hash_inputs
        def replaced(*args):
            result=hash_inputs(*args)
            replacement=obj.with_suffix('.replacement')
            replacement.write_bytes(obj.read_bytes());replacement.replace(obj)
            return result
        with patch.object(S,'hash_inputs',side_effect=replaced):
            with self.assertRaisesRegex(ValueError,'accepted object changed during input hashing'):
                self.validate_outputs(reference,ledger)

    def test_sidecar_is_bound_to_the_successful_physical_record(self):
        reference,snapshot,ledger,obj,receipt=self.aliased_outputs()
        value=json.loads(Path(receipt['path']).read_text())
        self.assertEqual(value['sidecar']['binding'],binding(obj.with_suffix('.vos')))
        self.assertEqual(value['sidecar_prestate']['state'],'absent')
        self.assertEqual(value['sidecar_status'],'compiled_output')
        self.assertEqual(Path(value['physical_result']['path']).stat().st_mode&0o777,0o600)
        report=self.validate_outputs(reference,ledger)
        marker=next(row for row in report['accepted_dependency_identities'] if row['kind']=='vos')
        self.assertEqual(marker['receipt'],receipt)
        self.assertEqual(marker['primary_object'],str(obj))
        self.assertEqual(marker['source'],binding(self.source))

    def test_absent_sidecar_cannot_appear_before_physical_dispatch(self):
        reference=self.seal()
        report=S.validate_compiler(self.runtime,self.reference,reference,self.source_binding,self.compiler)
        before=S.sidecar_prestate(self.source_binding,self.source.with_suffix('.vo'),
            binding(self.compiler),self.runtime['physical_flags'],report)
        self.source.with_suffix('.vos').write_bytes(b'')
        with self.assertRaisesRegex(ValueError,'sidecar appeared'):
            S.check_sidecar_prestate(before)

    def test_initial_bound_sidecar_is_not_this_runs_output(self):
        sidecar=self.source.with_suffix('.vos');sidecar.write_bytes(b'')
        self.runtime['bindings'].append(binding(sidecar))
        reference=self.seal()
        report=S.validate_compiler(self.runtime,self.reference,reference,self.source_binding,self.compiler)
        with self.assertRaisesRegex(ValueError,'preexisting compiler sidecar'):
            S.sidecar_prestate(self.source_binding,self.source.with_suffix('.vo'),
                binding(self.compiler),self.runtime['physical_flags'],report)

    def test_retained_sidecar_is_rechecked_immediately_before_dispatch(self):
        reference,snapshot,ledger,obj,receipt=self.aliased_outputs()
        report=self.validate_outputs(reference,ledger)
        before=S.sidecar_prestate(self.source_binding,obj,binding(self.compiler),self.runtime['physical_flags'],report)
        self.assertEqual(before['prior_receipt'],receipt)
        sidecar=obj.with_suffix('.vos');replacement=sidecar.with_suffix('.replacement')
        replacement.write_bytes(sidecar.read_bytes());replacement.replace(sidecar)
        with self.assertRaisesRegex(ValueError,'sidecar changed before compilation'):
            S.check_sidecar_prestate(before)

    def test_post_compile_sidecar_replacement_cannot_publish_receipt(self):
        reference,snapshot,ledger,obj,receipt=self.aliased_outputs()
        def replace(sidecar):
            other=sidecar.with_suffix('.replacement');other.write_bytes(sidecar.read_bytes());other.replace(sidecar)
        with self.assertRaisesRegex(ValueError,'output changed after its physical record'):
            self.accept_output(ledger,obj,before_accept=replace)
        self.assertEqual(len(ledger.rows),1)

    def test_changed_physical_record_refuses(self):
        reference,snapshot,ledger,obj,receipt=self.aliased_outputs()
        record=json.loads(Path(receipt['path']).read_text())
        Path(record['physical_result']['path']).write_text('{}')
        with self.assertRaisesRegex(ValueError,'snapshot hash differs'):
            self.validate_outputs(reference,ledger)

    def test_conflicting_object_hash_receipts_still_refuse(self):
        reference,snapshot,ledger,obj,receipt=self.aliased_outputs()
        obj.write_text('different physical output for the same source')
        self.accept_output(ledger,obj)
        self.assertNotEqual(json.loads(Path(ledger.rows[0]['path']).read_text())['object']['sha256'],
                            json.loads(Path(ledger.rows[1]['path']).read_text())['object']['sha256'])
        # Either the current-input guard or the conflicting-receipt guard must refuse.
        with self.assertRaises(ValueError):
            self.validate_outputs(reference,ledger)

    def test_changed_produced_object_refuses(self):
        reference, snapshot, ledger, obj, receipt = self.outputs()
        obj.write_text('tampered object')
        with self.assertRaisesRegex(ValueError, 'accepted compilation input changed'):
            self.validate_outputs(reference, ledger)

    def test_changed_receipt_refuses(self):
        reference, snapshot, ledger, obj, receipt = self.outputs()
        Path(receipt['path']).write_text('{}')
        with self.assertRaisesRegex(ValueError, 'snapshot hash differs'):
            self.validate_outputs(reference, ledger)

    def test_modified_index_refuses(self):
        reference, snapshot, ledger, obj, receipt = self.outputs()
        index = ledger.root / 'INDEX.json'
        value = json.loads(index.read_text())
        value['index']['receipts'] = []
        index.write_text(json.dumps(value))
        with self.assertRaisesRegex(ValueError, 'authentication differs'):
            self.validate_outputs(reference, ledger)

    def test_wrong_job_with_valid_authentication_refuses(self):
        reference, snapshot, ledger, obj, receipt = self.outputs()
        self.replace_index(ledger, 'runtime', dict(self.reference, sha256='0' * 64))
        with self.assertRaisesRegex(ValueError, 'another producer or job'):
            self.validate_outputs(reference, ledger)

    def test_wrong_producer_with_valid_authentication_refuses(self):
        reference, snapshot, ledger, obj, receipt = self.outputs()
        self.replace_index(ledger, 'producer', dict(snapshot['producer'], pid=0))
        with self.assertRaisesRegex(ValueError, 'another producer or job'):
            self.validate_outputs(reference, ledger)

    def replace_index(self, ledger, field, selected):
        import hmac
        path = ledger.root / 'INDEX.json'
        value = json.loads(path.read_text())
        value['index'][field] = selected
        value['mac'] = hmac.new(bytes.fromhex(ledger.key), S._encoded(value['index']), 'sha256').hexdigest()
        S._publish(path, value, replace=True)

    def test_missing_receipt_refuses(self):
        reference, snapshot, ledger, obj, receipt = self.outputs()
        Path(receipt['path']).unlink()
        with self.assertRaisesRegex(ValueError, 'stale or a receipt is absent'):
            self.validate_outputs(reference, ledger)

    def test_stale_index_refuses(self):
        reference = self.seal()
        snapshot = self.read(reference)
        ledger = S.OutputReceipts(snapshot, reference)
        old = (ledger.root / 'INDEX.json').read_bytes()
        obj = self.source.with_suffix('.vo')
        obj.write_text('nonproof output')
        self.accept_output(ledger,obj)
        (ledger.root / 'INDEX.json').write_bytes(old)
        with self.assertRaisesRegex(ValueError, 'stale or a receipt is absent'):
            self.validate_outputs(reference, ledger)

    def test_new_dependency_without_receipt_refuses(self):
        reference = self.seal()
        (self.library / 'Unaccepted.vo').write_text('unaccepted output')
        with self.assertRaisesRegex(ValueError, 'lacks a validated receipt'):
            S.validate_compiler(self.runtime, self.reference, reference, self.source_binding, self.compiler)

    def test_failure_cannot_publish_receipt(self):
        reference = self.seal()
        snapshot = self.read(reference)
        ledger = S.OutputReceipts(snapshot, reference)
        with self.assertRaisesRegex(ValueError, 'failed compilation'):
            ledger.accept(self.source, self.obj, self.compiler, [], {'success': False})
        self.assertEqual(list(ledger.root.glob('OBJECT-*.json')), [])

    def test_other_producer_cannot_publish_receipt(self):
        reference = self.seal()
        ledger = S.OutputReceipts(self.read(reference), reference)
        with patch.object(S, 'producer', return_value={'pid': 0}):
            with self.assertRaisesRegex(ValueError, 'Another producer'):
                ledger.accept(self.source, self.obj, self.compiler, [], {'success': True})

    def test_changed_direct_source_refuses(self):
        reference = self.seal()
        self.source.write_text('changed source')
        with self.assertRaisesRegex(ValueError, 'identity changed'):
            S.validate_compiler(self.runtime, self.reference, reference, self.source_binding, self.compiler)

    def test_changed_compiler_bytes_refuse(self):
        reference = self.seal()
        self.compiler.write_text('changed compiler')
        with self.assertRaisesRegex(ValueError, 'identity changed'):
            S.validate_compiler(self.runtime, self.reference, reference, self.source_binding, self.compiler)

    def test_mapping_alias_cannot_select_other_already_bound_objects(self):
        alternate = self.root / 'alternate'
        alternate.mkdir()
        other = alternate / self.obj.name
        other.write_text('another historical bound object')
        self.runtime['bindings'].append(binding(other))
        alias = self.root / 'load-path'
        alias.symlink_to(self.library, target_is_directory=True)
        self.runtime['physical_flags'] = ['-Q', str(alias), 'Example']
        reference = self.seal()
        alias.unlink()
        alias.symlink_to(alternate, target_is_directory=True)
        with self.assertRaisesRegex(ValueError, 'mapping namespace changed'):
            S.validate_compiler(self.runtime, self.reference, reference, self.source_binding, self.compiler)

    def test_mapping_change_during_initial_validation_refuses(self):
        self.runtime['physical_flags'] = ['-I', str(self.library)]
        def mutate():
            self.library.chmod(0o700)
        with self.assertRaisesRegex(ValueError, 'mapping changed during full validation'):
            self.seal(mutate)
        self.assertFalse(self.snapshot_path.exists())

    def test_new_directory_entry_does_not_change_mapping_identity(self):
        before = S.mapping_context(self.runtime['physical_flags'])
        (self.library / 'Unrelated.log').write_text('new noninput')
        self.assertEqual(S.mapping_context(self.runtime['physical_flags']), before)

    def test_new_cma_without_original_binding_or_receipt_refuses(self):
        reference=self.seal()
        (self.library/'Unaccepted.cma').write_text('nonproof plugin fixture')
        with self.assertRaisesRegex(ValueError,'lacks a validated receipt'):
            S.validate_compiler(self.runtime,self.reference,reference,self.source_binding,self.compiler)

    def test_new_shared_library_without_original_binding_or_receipt_refuses(self):
        reference=self.seal()
        (self.library/'Unaccepted.so').write_text('nonproof library fixture')
        with self.assertRaisesRegex(ValueError,'lacks a validated receipt'):
            S.validate_compiler(self.runtime,self.reference,reference,self.source_binding,self.compiler)

    def test_generated_source_must_match_the_pre_admission_binding(self):
        reference=self.seal()
        generated=self.root/'Generated.v'
        generated.write_text('original generated test input')
        expected=binding(generated)
        generated.write_text('changed during admission')
        with self.assertRaisesRegex(ValueError,'recorded physical source changed during admission'):
            S.validate_compiler(self.runtime,self.reference,reference,expected,self.compiler)

    def initial_objects(self):
        root=self.compiler.parent.parent/'lib/coq/theories/Arith'
        root.mkdir(parents=True)
        paths=[root/('Arith'+suffix) for suffix in ['.vo','.vos']]
        for path in paths:path.write_text('initial nonproof object fixture '+path.suffix)
        return paths

    def test_initial_unbound_library_objects_are_sealed_and_accepted(self):
        paths=self.initial_objects()
        reference=self.seal()
        snapshot=self.read(reference)
        self.assertEqual({row['path'] for row in snapshot['initial_objects']},{str(path) for path in paths})
        for row in snapshot['initial_objects']:
            self.assertEqual(row['identity'],S._identity(row['path']))
            self.assertEqual(row['sha256'],binding(row['path'])['sha256'])
        self.assertEqual(len(snapshot['rows']),4)
        report=S.validate_compiler(self.runtime,self.reference,reference,self.source_binding,self.compiler)
        self.assertEqual(report['initial_objects_checked'],2)
        self.assertEqual(len(report['directly_hashed_inputs']),5)

    def test_initial_library_object_mutation_refuses(self):
        paths=self.initial_objects();reference=self.seal()
        paths[0].write_text('changed initial object')
        with self.assertRaisesRegex(ValueError,'compiler input identity changed'):
            S.validate_compiler(self.runtime,self.reference,reference,self.source_binding,self.compiler)

    def test_initial_library_object_restored_mtime_still_refuses(self):
        paths=self.initial_objects();reference=self.seal();old=paths[0].stat()
        paths[0].write_bytes(b'x'*old.st_size)
        os.utime(paths[0],ns=(old.st_atime_ns,old.st_mtime_ns))
        with self.assertRaisesRegex(ValueError,'compiler input identity changed'):
            S.validate_compiler(self.runtime,self.reference,reference,self.source_binding,self.compiler)

    def test_initial_library_object_replacement_refuses(self):
        paths=self.initial_objects();reference=self.seal()
        replacement=paths[0].with_suffix('.replacement');replacement.write_bytes(paths[0].read_bytes())
        os.replace(replacement,paths[0])
        with self.assertRaisesRegex(ValueError,'compiler input identity changed'):
            S.validate_compiler(self.runtime,self.reference,reference,self.source_binding,self.compiler)

    def test_later_installed_object_addition_still_requires_receipt(self):
        paths=self.initial_objects();reference=self.seal()
        (paths[0].parent/'Later.vo').write_text('later nonproof object')
        with self.assertRaisesRegex(ValueError,'lacks a validated receipt'):
            S.validate_compiler(self.runtime,self.reference,reference,self.source_binding,self.compiler)

    def test_initial_object_mutation_during_full_validation_refuses(self):
        paths=self.initial_objects()
        with self.assertRaisesRegex(ValueError,'initial object changed during full validation'):
            self.seal(lambda:paths[0].write_text('changed during initial validation'))
        self.assertFalse(self.snapshot_path.exists())

    def test_object_addition_during_full_validation_refuses(self):
        paths=self.initial_objects()
        with self.assertRaisesRegex(ValueError,'mapping changed during full validation'):
            self.seal(lambda:(paths[0].parent/'Later.vo').write_text('new while validation ran'))
        self.assertFalse(self.snapshot_path.exists())

    def test_canonical_binding_covers_initial_object_alias(self):
        paths=self.initial_objects();self.runtime['bindings'].extend(binding(path) for path in paths)
        alias=self.root/'stdlib-alias';alias.symlink_to(paths[0].parent,target_is_directory=True)
        self.runtime['physical_flags']+=['-Q',str(alias),'Alias']
        reference=self.seal()
        self.assertEqual(self.read(reference)['initial_objects'],[])
        S.validate_compiler(self.runtime,self.reference,reference,self.source_binding,self.compiler)

    def test_legacy_snapshot_cannot_invent_initial_object_authentication(self):
        self.initial_objects();reference=self.seal();value=self.read(reference)
        value.pop('initial_objects');S._publish(self.snapshot_path,value,replace=True)
        reference=binding(self.snapshot_path)
        with self.assertRaisesRegex(ValueError,'lacks an original binding'):
            S.validate_compiler(self.runtime,self.reference,reference,self.source_binding,self.compiler)

    def initial_plugins(self):
        root=self.compiler.parent.parent/'lib/coq-core/boot'
        root.mkdir(parents=True)
        paths=[root/('boot'+suffix) for suffix in ['.cma','.cmxs','.so']]
        for path in paths:path.write_text('initial nonproof plugin fixture '+path.suffix)
        return paths

    def test_initial_unbound_plugins_are_sealed_and_accepted(self):
        paths=self.initial_plugins()
        reference=self.seal()
        snapshot=self.read(reference)
        self.assertEqual({row['path'] for row in snapshot['initial_plugins']},{str(path) for path in paths})
        self.assertEqual(len(snapshot['rows']),4)
        report=S.validate_compiler(self.runtime,self.reference,reference,self.source_binding,self.compiler)
        self.assertEqual(report['initial_plugins_checked'],3)
        self.assertEqual(len(report['directly_hashed_inputs']),6)

    def test_initial_sealed_plugin_mutation_refuses(self):
        paths=self.initial_plugins()
        reference=self.seal()
        paths[0].write_text('changed plugin')
        with self.assertRaisesRegex(ValueError,'compiler input identity changed'):
            S.validate_compiler(self.runtime,self.reference,reference,self.source_binding,self.compiler)

    def test_later_plugin_addition_still_requires_a_validated_receipt(self):
        paths=self.initial_plugins()
        reference=self.seal()
        (paths[0].parent/'late.cma').write_text('later nonproof plugin')
        with self.assertRaisesRegex(ValueError,'lacks a validated receipt'):
            S.validate_compiler(self.runtime,self.reference,reference,self.source_binding,self.compiler)

    def test_initial_plugin_mutation_during_full_validation_refuses(self):
        paths=self.initial_plugins()
        with self.assertRaisesRegex(ValueError,'initial plugin changed during full validation'):
            self.seal(lambda:paths[0].write_text('changed while validation ran'))
        self.assertFalse(self.snapshot_path.exists())

    def test_selected_compiler_alias_cannot_select_another_bound_binary(self):
        original=self.compiler.with_name('original')
        self.compiler.rename(original)
        self.compiler.symlink_to(original)
        alternate=self.compiler.with_name('alternate')
        alternate.write_text('another bound compiler fixture')
        self.runtime['physical_compiler']=binding(original)
        self.runtime['bindings'][-1]=binding(original)
        self.runtime['bindings'].append(binding(alternate))
        reference=self.seal()
        self.compiler.unlink()
        self.compiler.symlink_to(alternate)
        with self.assertRaisesRegex(ValueError,'selected compiler identity changed'):
            S.validate_compiler(self.runtime,self.reference,reference,self.source_binding,self.compiler)

    def test_incorrect_pinned_compiler_hash_refuses_before_publication(self):
        self.runtime['physical_compiler']=dict(self.runtime['physical_compiler'],sha256='0'*64)
        with self.assertRaisesRegex(ValueError,'selected compiler differs from its bound physical identity'):
            self.seal()
        self.assertFalse(self.snapshot_path.exists())


if __name__ == '__main__':
    unittest.main()
