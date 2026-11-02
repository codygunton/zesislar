"""Keep Sail source context local and authenticate its physical receipt flags."""
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

import compiler_snapshot as S
from entry_chain import binding, save
from source_context import compilation, effective_flags
import test_compiler_snapshot as snapshot_fixtures


class SourceContextTests(unittest.TestCase):
    def setUp(self):
        self.temp=tempfile.TemporaryDirectory();self.addCleanup(self.temp.cleanup)
        self.root=Path(self.temp.name);self.library=self.root/'sail';self.library.mkdir()
        self.source=self.library/'TypeCasts.v';self.source.write_text('Require Export Inhabited.\n')
        self.flags=['-boot','-Q',str(self.library),'SailStdpp','-Q',str(self.root/'other'),'Other']

    def test_only_own_sail_root_changes(self):
        before=list(self.flags)
        context=compilation(self.flags,binding(self.source))
        self.assertEqual(context['physical_flags'],['-boot','-R',str(self.library),'SailStdpp','-Q',str(self.root/'other'),'Other'])
        self.assertEqual(context['base_flags'],before)
        self.assertEqual(self.flags,before)
        self.assertEqual(self.source.read_text(),'Require Export Inhabited.\n')

    def test_outside_source_keeps_global_q(self):
        outside=self.root/'Consumer.v';outside.write_text('From Coq Require Import String.\n')
        self.assertEqual(effective_flags(self.flags,binding(outside)),self.flags)
        self.assertEqual(compilation(self.flags,binding(outside))['changes'],[])

    def test_other_namespace_keeps_q(self):
        flags=['-Q',str(self.library),'Other']
        self.assertEqual(effective_flags(flags,binding(self.source)),flags)

    def test_changed_sail_source_refuses(self):
        source=binding(self.source);self.source.write_text('changed')
        with self.assertRaisesRegex(ValueError,'source context changed'):
            effective_flags(self.flags,source)

    def test_already_recursive_mapping_stays_exact(self):
        flags=['-R',str(self.library),'SailStdpp']
        self.assertEqual(effective_flags(flags,binding(self.source)),flags)

    def test_conflicting_sail_context_refuses(self):
        flags=self.flags+['-Q',str(self.root),'SailStdpp']
        with self.assertRaisesRegex(ValueError,'conflicting Sail'):
            effective_flags(flags,binding(self.source))

    def test_missing_source_binding_refuses(self):
        with self.assertRaises(ValueError):compilation(self.flags,{'path':str(self.source)})

    def test_incomplete_mapping_refuses(self):
        with self.assertRaisesRegex(ValueError,'mapping is incomplete'):
            effective_flags(['-Q',str(self.library)],binding(self.source))

    def test_isolated_staged_helper_needs_no_harness_path(self):
        owned=self.root/'owned/tools/block';owned.mkdir(parents=True)
        original=Path(__file__).parent/'code/source_context.py'
        (owned/'source_context.py').write_bytes(original.read_bytes())
        program='import sys;sys.path.insert(0,sys.argv[1]);import source_context;print(source_context.__file__)'
        result=subprocess.run([sys.executable,'-I','-B','-c',program,str(owned)],
                              capture_output=True,text=True,check=True)
        self.assertEqual(Path(result.stdout.strip()),owned/'source_context.py')


class SourceContextReceiptTests(unittest.TestCase):
    def setUp(self):
        self.fixture=snapshot_fixtures.CompilerSnapshotTests();self.fixture.setUp()
        self.addCleanup(self.fixture.temp.cleanup);f=self.fixture
        source=f.library/'TypeCasts.v';f.source.rename(source);f.source=source
        f.source_binding=binding(source)
        (f.library/'Dependency.v').write_text('(* Nonproof dependency fixture. *)\n')
        f.runtime['physical_flags']=['-Q',str(f.library),'SailStdpp']
        self.graph=f.root/'GRAPH.json';save(self.graph,{'import_edges':[{'from':'SailStdpp.TypeCasts','to':'SailStdpp.Inhabited'}]})
        f.runtime.update(module_files={'SailStdpp.TypeCasts':'library/TypeCasts.v',
                        'SailStdpp.Inhabited':'library/Dependency.v'},cache_import_graph=binding(self.graph))
        f.runtime['bindings']=[binding(f.source),binding(f.obj),binding(f.compiler),binding(self.graph)]
        self.reference=f.seal();self.manager=S.OutputReceipts(self.reference,f.reference)
        self.report=S.validate_compiler(f.runtime,f.reference,self.reference,binding(f.source),f.compiler)

    def physical(self, *, wrong_context=False, missing_context=False):
        f=self.fixture;source=binding(f.source);compiler=binding(f.compiler)
        context=compilation(f.runtime['physical_flags'],source);flags=context['physical_flags']
        report=dict(self.report,import_selection=S.import_selection(f.runtime,source,f.root,self.report))
        directory=f.root/'compiler-invocations'/'synthetic';directory.mkdir(parents=True)
        validation=S._publish(directory/'PHYSICAL-VALIDATION.json',report)
        obj=f.source.with_suffix('.vo');obj.write_bytes(b'nonproof compiled fixture')
        before=S.sidecar_prestate(source,obj,compiler,flags,self.report)
        obj.with_suffix('.vos').write_bytes(b'')
        argv=[compiler['path'],*flags,source['path']]
        recorded=dict(context)
        if wrong_context:recorded['physical_flags']=f.runtime['physical_flags']
        input_record=dict(source=source,compiler=compiler,
            owned_workspace=str(f.root),physical_argv=argv,compiler_context=recorded,
            sidecar_prestate=before,validation={'runtime':f.reference,'snapshot':self.reference})
        if missing_context:input_record.pop('compiler_context')
        inputs=S._publish(directory/'INPUT.json',input_record)
        physical=S._publish(directory/'PHYSICAL-RESULT.json',dict(input=inputs,input_validation=validation,
            physical_argv=argv,returncode=0,output_capture={'complete':True},
            output_validation={'success':True},compiler_outputs=S.compiler_outputs(obj,before)))
        return obj,physical

    def test_validation_keeps_base_flags_and_binds_effective_flags(self):
        f=self.fixture
        self.assertEqual(f.runtime['physical_flags'][0],'-Q')
        self.assertEqual(self.report['physical_flags'][0],'-R')
        self.assertEqual(self.report['compiler_context']['source'],binding(f.source))

    def test_sail_receipt_and_reuse_share_effective_context(self):
        from object_imports import compatibility
        f=self.fixture;obj,physical=self.physical()
        accepted=self.manager.accept(f.source,obj,f.compiler,f.runtime['physical_flags'],{'success':True},physical_result=physical)
        receipt=json.loads(Path(accepted['path']).read_text())
        self.assertEqual(receipt['normalized_flags'][0],'-R')
        self.assertEqual(receipt['compiler_context']['base_flags'][0],'-Q')
        snapshot=S.read(self.reference,f.reference)
        rows,_,_,_=S.accepted_objects(snapshot,self.reference,self.manager.key,binding(f.compiler),f.runtime['physical_flags'])
        self.assertEqual(rows,[binding(obj)])
        result=compatibility(['SailStdpp.TypeCasts'],json.loads(self.graph.read_text())['import_edges'],
            f.runtime['module_files'],f.root,{'SailStdpp.TypeCasts':accepted},binding(f.compiler),f.runtime['physical_flags'])
        self.assertIn('SailStdpp.TypeCasts',result['compatible_owned_modules'])

    def test_wrong_recorded_physical_context_refuses(self):
        f=self.fixture;obj,physical=self.physical(wrong_context=True)
        with self.assertRaisesRegex(ValueError,'source context'):
            self.manager.accept(f.source,obj,f.compiler,f.runtime['physical_flags'],{'success':True},physical_result=physical)

    def test_missing_changed_physical_context_refuses(self):
        f=self.fixture;obj,physical=self.physical(missing_context=True)
        with self.assertRaisesRegex(ValueError,'source context'):
            self.manager.accept(f.source,obj,f.compiler,f.runtime['physical_flags'],{'success':True},physical_result=physical)

    def test_sail_receipt_relocates_with_effective_flags(self):
        from clone_copy import copy2
        from object_imports import compatibility
        f=self.fixture;obj,physical=self.physical()
        accepted=self.manager.accept(f.source,obj,f.compiler,f.runtime['physical_flags'],{'success':True},physical_result=physical)
        copied=f.root/'relocated';(copied/'library').mkdir(parents=True)
        for source in [f.source,obj,f.obj,f.library/'Dependency.v']:
            copy2(source,copied/source.relative_to(f.root))
        result=compatibility(['SailStdpp.TypeCasts'],json.loads(self.graph.read_text())['import_edges'],
            f.runtime['module_files'],copied,{'SailStdpp.TypeCasts':accepted},binding(f.compiler),
            ['-Q',str(copied/'library'),'SailStdpp'])
        self.assertIn('SailStdpp.TypeCasts',result['compatible_owned_modules'])


if __name__=='__main__':unittest.main()
