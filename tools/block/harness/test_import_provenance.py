"""Authenticate imported object hashes with nonproof compiler receipt fixtures."""
import json
from pathlib import Path
import unittest

import compiler_snapshot as S
from entry_chain import binding, save
import test_compiler_snapshot as fixture


class ImportProvenanceTests(unittest.TestCase):
    def setUp(self):
        self.fixture=fixture.CompilerSnapshotTests()
        self.fixture.setUp()
        self.addCleanup(self.fixture.temp.cleanup)
        f=self.fixture
        self.root=f.root
        self.dependency=f.obj
        (f.library/'Dependency.v').write_text('Require Import Example.Leaf.\n')
        (f.library/'Leaf.v').write_text('(* Nonproof source fixture. *)\n')
        self.leaf=f.library/'Leaf.vo';self.leaf.write_bytes(b'leaf object fixture')
        self.graph=self.root/'GRAPH.json'
        save(self.graph,{'import_edges':[{'from':'Example.Control','to':'Example.Dependency'},
                                        {'from':'Example.Dependency','to':'Example.Leaf'}]})
        f.runtime.update(module_files={'Example.Control':'Control.v',
            'Example.Dependency':'library/Dependency.v','Example.Leaf':'library/Leaf.v'},
            cache_import_graph=binding(self.graph))
        f.runtime['bindings'].extend([binding(self.graph),binding(self.leaf)])
        self.reference=f.seal()
        self.manager=S.OutputReceipts(self.reference,f.reference)
        self.report=S.validate_compiler(f.runtime,f.reference,self.reference,
                                       binding(f.source),f.compiler)

    def selection(self):
        return S.import_selection(self.fixture.runtime,binding(self.fixture.source),
                                  self.root,self.report)

    def physical(self, mutate_report=None, validation_path=None):
        f=self.fixture;source=binding(f.source);compiler=binding(f.compiler)
        selection=self.selection()
        report={**self.report,'import_selection':selection}
        if mutate_report:mutate_report(report)
        directory=self.root/'compiler-invocations'/'synthetic'
        directory.mkdir(parents=True)
        validation=S._publish(validation_path or directory/'PHYSICAL-VALIDATION.json',report)
        obj=f.source.with_suffix('.vo');obj.write_bytes(b'nonproof produced object')
        before=S.sidecar_prestate(source,obj,compiler,f.runtime['physical_flags'],self.report)
        obj.with_suffix('.vos').write_bytes(b'')
        argv=[compiler['path'],*f.runtime['physical_flags'],source['path']]
        inputs=S._publish(directory/'INPUT.json',dict(source=source,compiler=compiler,
            owned_workspace=str(self.root),physical_argv=argv,sidecar_prestate=before,
            validation={'runtime':f.reference,'snapshot':self.reference}))
        result=S._publish(directory/'PHYSICAL-RESULT.json',dict(input=inputs,
            input_validation=validation,physical_argv=argv,returncode=0,
            output_capture={'complete':True},output_validation={'success':True},
            compiler_outputs=S.compiler_outputs(obj,before)))
        return obj,result,validation

    def accept(self, obj, result):
        f=self.fixture
        return self.manager.accept(f.source,obj,f.compiler,f.runtime['physical_flags'],
                                   {'success':True},physical_result=result)

    def test_transitive_inputs_use_validated_hashes(self):
        selected=self.selection()
        self.assertEqual([row['module'] for row in selected['imported_objects']],
                         ['Example.Dependency','Example.Leaf'])
        self.assertEqual(selected['imported_objects'][0]['object'],binding(self.dependency))
        self.assertEqual(selected['imported_objects'][1]['object'],binding(self.leaf))

    def test_receipt_binds_physical_validation_and_produced_object(self):
        obj,physical,validation=self.physical()
        reference=self.accept(obj,physical)
        receipt=json.loads(Path(reference['path']).read_text())
        imports=receipt['import_provenance']
        self.assertEqual(imports['schema'],'entry-chain.object-imports.v1')
        self.assertEqual(imports['module'],'Example.Control')
        self.assertEqual(imports['validation'],validation)
        self.assertEqual(imports['normalized_flags'],['-Q','{workspace}/library','Example'])
        self.assertEqual(imports['compiler'],binding(self.fixture.compiler))
        self.assertEqual(receipt['object'],binding(obj))
        self.assertEqual(receipt['physical_result'],physical)
        snapshot=S.read(self.reference,self.fixture.reference)
        rows,_,_,_=S.accepted_objects(snapshot,self.reference,self.manager.key,
                                     binding(self.fixture.compiler),self.fixture.runtime['physical_flags'])
        self.assertEqual(rows,[binding(obj)])

    def test_changed_import_identity_refuses(self):
        selection=self.selection()
        self.dependency.write_bytes(b'changed object fixture')
        with self.assertRaisesRegex(ValueError,'imported compiler object changed'):
            S.check_import_selection(selection,self.report)

    def test_missing_validated_import_refuses(self):
        report={**self.report,'directly_hashed_inputs':[row for row in self.report['directly_hashed_inputs']
                                                      if row['path']!=str(self.leaf)]}
        with self.assertRaisesRegex(ValueError,'lacks its validated'):
            S.import_selection(self.fixture.runtime,binding(self.fixture.source),self.root,report)

    def test_changed_graph_binding_refuses(self):
        self.graph.write_text('{"import_edges":[]}')
        with self.assertRaises(ValueError):self.selection()

    def test_no_graph_grants_no_reuse_provenance(self):
        runtime={**self.fixture.runtime};runtime.pop('cache_import_graph')
        self.assertIsNone(S.import_selection(runtime,binding(self.fixture.source),self.root,self.report))

    def test_unmapped_verification_source_grants_no_reuse_provenance(self):
        source=self.root/'Verification.v';source.write_text('(* Nonproof verification fixture. *)')
        self.assertIsNone(S.import_selection(self.fixture.runtime,binding(source),self.root,self.report))

    def test_two_owner_modules_refuse(self):
        self.fixture.runtime['module_files']['Alias.Control']='Control.v'
        with self.assertRaisesRegex(ValueError,'one canonical owner'):self.selection()

    def test_pinned_external_mapping_retains_existing_input_validation(self):
        self.fixture.runtime['module_files']['Example.Leaf']='/foreign/Leaf.v'
        self.assertEqual([row['module'] for row in self.selection()['imported_objects']],['Example.Dependency'])
        self.assertIn(str(self.leaf),[row['path'] for row in self.report['directly_hashed_inputs']])

    def test_owned_mapping_escape_refuses(self):
        import tempfile
        with tempfile.TemporaryDirectory() as directory:
            (self.root/'escape').symlink_to(directory,target_is_directory=True)
            self.fixture.runtime['module_files']['Example.Leaf']='escape/Leaf.v'
            with self.assertRaisesRegex(ValueError,'leaves its workspace'):self.selection()

    def test_canonical_import_paths_match_alias_report(self):
        alias=self.root/'alias';alias.symlink_to(self.fixture.library,target_is_directory=True)
        for row in self.report['directly_hashed_inputs']:
            if row['path']==str(self.dependency):row['path']=str(alias/self.dependency.name)
        selected=self.selection()
        self.assertEqual(selected['imported_objects'][0]['object'],binding(self.dependency))
        S.check_import_selection(selected,self.report)

    def test_changed_validation_report_refuses_acceptance(self):
        obj,physical,validation=self.physical()
        Path(validation['path']).write_text('{}')
        with self.assertRaisesRegex(ValueError,'hash differs'):self.accept(obj,physical)

    def test_changed_recorded_selection_refuses_acceptance(self):
        obj,physical,_=self.physical(lambda report:report['import_selection']['imported_objects'].clear())
        with self.assertRaisesRegex(ValueError,'import selection differs'):self.accept(obj,physical)

    def test_other_invocation_validation_refuses_acceptance(self):
        obj,physical,_=self.physical(validation_path=self.root/'OTHER-VALIDATION.json')
        with self.assertRaisesRegex(ValueError,'leaves its compiler invocation'):self.accept(obj,physical)

    def test_actual_producer_receipt_passes_the_reuse_consumer(self):
        from object_imports import compatibility
        obj,physical,_=self.physical()
        receipt=self.accept(obj,physical)
        runtime=self.fixture.runtime
        result=compatibility(['Example.Control'],json.loads(self.graph.read_text())['import_edges'],
            runtime['module_files'],self.root,{'Example.Control':receipt},
            binding(self.fixture.compiler),runtime['physical_flags'])
        self.assertIn('Example.Control',result['compatible_owned_modules'])

    def test_actual_receipt_relocates_and_detects_changed_import(self):
        from clone_copy import copy2
        from object_imports import compatibility
        obj,physical,_=self.physical()
        receipt=self.accept(obj,physical)
        copied=self.root/'relocated';(copied/'library').mkdir(parents=True)
        for source in [self.fixture.source,obj,self.dependency,self.leaf,
                       self.fixture.library/'Dependency.v',self.fixture.library/'Leaf.v']:
            copy2(source,copied/source.relative_to(self.root))
        runtime=self.fixture.runtime
        arguments=(['Example.Control'],json.loads(self.graph.read_text())['import_edges'],
                   runtime['module_files'],copied,{'Example.Control':receipt},
                   binding(self.fixture.compiler),['-Q',str(copied/'library'),'Example'])
        result=compatibility(*arguments)
        self.assertIn('Example.Control',result['compatible_owned_modules'])
        (copied/'library/Leaf.vo').write_bytes(b'changed imported object')
        result=compatibility(*arguments)
        self.assertIn('Example.Control',result['rebuild_modules'])


if __name__=='__main__':unittest.main()
