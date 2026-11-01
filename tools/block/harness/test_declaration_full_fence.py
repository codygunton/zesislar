"""Check full-fence declaration booking without a compiler or a live claim."""
from copy import deepcopy
from pathlib import Path
import ast
import fcntl
import hashlib
import json
import os
import sys
import tempfile
import unittest

HERE=Path(__file__).resolve().parent
sys.path[:0]=[str(HERE/'code'),str(HERE),str(HERE.parent),str(HERE.parents[1])]
import memory_policy as P


def binding(path):
    return {'path':str(path),'sha256':hashlib.sha256(path.read_bytes()).hexdigest()}


class DeclarationFullFenceTests(unittest.TestCase):
    def setUp(self):
        temporary=tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.root=Path(temporary.name)
        self.sources=[]
        self.modules={}
        for name in ['First','Second']:
            path=self.root/(name+'.v')
            path.write_text('Definition fixture_data := True.\n')
            module='Fixture.'+name
            self.sources.append(dict(binding(path),module=module,role='generated_declarations'))
            self.modules[module]=str(path)
        self.profile={'schema':'scratch.admission-profile.v1','kind':P.FOCUSED_KIND,
                      'sources':self.sources,'memory_booking':'full_physical_fence'}
        self.config={'declarations_only':True,'prepared_workspace':str(self.root),
                     'proof_runtime':{'module_files':self.modules}}
        self.raw={'phase':'prerequisites','ordered_modules':list(self.modules)}

    def profile_binding(self):
        path=self.root/'PROFILE.json'
        path.write_text(json.dumps(self.profile))
        return binding(path)

    def workload(self):
        return P.workload_for_job(self.profile_binding(),self.raw,self.config)

    def job(self):
        return P.apply_job(self.raw,workload=self.workload())

    def test_each_declaration_phase_books_its_unchanged_fence(self):
        for phase in ['prerequisites','compile_only','kernel']:
            with self.subTest(phase=phase):
                self.raw['phase']=phase
                job=self.job()
                self.assertEqual(P.validate_job(job),64*P.GIB)
                self.assertEqual(job['physical_fence_bytes'],64*P.GIB)
                for claim in [None,64*P.GIB]:
                    env=P.environment(phase,claim,job=job)
                    self.assertEqual(env['ZESU_MODULE_CLAIM_BYTES'],str(64*P.GIB))
                    self.assertEqual(env['ZESU_AGGREGATE_LIMIT'],'64G')
                    self.assertEqual(env['ZESU_SCOPE_CPU'],'unlimited')
                policy=dict(memory_job=job,minimum_claim_bytes=64*P.GIB,
                            physical_fence_bytes=64*P.GIB)
                self.assertEqual(P.admission_claim(policy),64*P.GIB)

    def test_option_only_raises_existing_claims(self):
        full=self.job()
        self.profile.pop('memory_booking')
        focused=self.job()
        ordinary=P.apply_job(self.raw)
        self.assertEqual(focused['claim_bytes'],8*P.GIB)
        self.assertEqual(ordinary['claim_bytes'],24*P.GIB)
        self.assertGreater(full['claim_bytes'],focused['claim_bytes'])
        self.assertGreater(full['claim_bytes'],ordinary['claim_bytes'])
        self.assertEqual(full['physical_fence_bytes'],focused['physical_fence_bytes'])
        self.assertEqual(full['physical_fence_bytes'],ordinary['physical_fence_bytes'])

    def test_non_declaration_focused_profile_refuses(self):
        for value in [False,None,1]:
            with self.subTest(declarations_only=value):
                self.config['declarations_only']=value
                with self.assertRaisesRegex(ValueError,'requires declaration-only execution'):
                    self.workload()
        self.config['declarations_only']=True
        self.raw['phase']='native'
        with self.assertRaisesRegex(ValueError,'requires declaration-only execution'):
            self.workload()

    def test_invalid_booking_values_refuse(self):
        for value in [None,False,True,0,24*P.GIB,64*P.GIB,'full_fence',{},[]]:
            with self.subTest(value=value):
                self.profile['memory_booking']=value
                with self.assertRaisesRegex(ValueError,'booking option is invalid'):
                    self.workload()

    def test_changed_fence_and_underbooking_refuse(self):
        job=self.job()
        for fence in [32*P.GIB,128*P.GIB]:
            wrong=deepcopy(job)
            wrong['physical_fence_bytes']=fence
            with self.assertRaisesRegex(ValueError,'claim or physical fence'):
                P.validate_job(wrong)
        wrong=deepcopy(job)
        wrong['claim_bytes']=24*P.GIB
        with self.assertRaisesRegex(ValueError,'claim or physical fence'):
            P.validate_job(wrong)
        with self.assertRaisesRegex(ValueError,'differs from full-fence booking'):
            P.environment('prerequisites',24*P.GIB,job=job)
        with self.assertRaisesRegex(ValueError,'Admission differs'):
            P.admission_claim(dict(memory_job=job,minimum_claim_bytes=24*P.GIB,
                                   physical_fence_bytes=64*P.GIB))

    def test_exact_source_coverage_remains_required(self):
        self.raw['ordered_modules'].append('Fixture.Missing')
        with self.assertRaisesRegex(ValueError,'every compiled module'):
            self.workload()
        self.raw['ordered_modules']=list(self.modules)
        self.profile['sources']=self.sources[:1]
        with self.assertRaisesRegex(ValueError,'every compiled module'):
            self.workload()

    def test_changed_source_and_native_proof_still_refuse(self):
        path=Path(self.sources[0]['path'])
        path.write_text('Definition changed := False.\n')
        with self.assertRaises(ValueError):
            self.workload()
        path.write_text('Lemma forbidden : True. Proof. zesu_block. Qed.\n')
        self.sources[0].update(binding(path))
        with self.assertRaisesRegex(ValueError,'contains a native proof'):
            self.workload()

    def test_provider_preserves_the_full_booking(self):
        tree=ast.parse((HERE/'code/entry_chain_provider.py').read_text())
        function=next(x for x in tree.body if isinstance(x,ast.FunctionDef)
                      and x.name=='prerequisite_environment')
        namespace=dict(os=os,relative=Path)
        exec(compile(ast.fix_missing_locations(ast.Module(body=[function],type_ignores=[])),
                     '<declaration-provider-environment>','exec'),namespace)
        runtime=dict(phase='prerequisites',coqc_wrapper='tools/entry_chain_coqc.sh',
                     build_dir='default',ocamlpath='{workspace}/lib',runtime_path='runtime',
                     runtime_sha256='sha',canonical_admission={'minimum_claim_bytes':64*P.GIB})
        env=namespace['prerequisite_environment'](runtime,self.root,self.root,inherited={})
        self.assertEqual(env['ZESU_MODULE_CLAIM_BYTES'],str(64*P.GIB))
        self.assertEqual(env['ZESU_MODULE_LIMIT_GIB'],'64')

    def test_actual_reserve_records_sixtyfour_in_a_temporary_ledger(self):
        tree=ast.parse((HERE/'code/check_entry_outside.py').read_text())
        function=next(x for x in tree.body if isinstance(x,ast.FunctionDef) and x.name=='reserve')
        ledger=self.root/'ledger.json'
        ledger.write_text(json.dumps({'fixed_claims':{}}))
        def save(path,value):
            Path(path).write_text(json.dumps(value))
        namespace=dict(Path=Path,fcntl=fcntl,time=__import__('time'),strict_loads=json.loads,
                       atomic_json=save,digest=lambda path:binding(Path(path))['sha256'],
                       canonical_functions=lambda policy:(lambda data,legacy:{},lambda:200*P.GIB))
        exec(compile(ast.fix_missing_locations(ast.Module(body=[function],type_ignores=[])),
                     '<declaration-reserve>','exec'),namespace)
        job=self.job()
        policy=dict(memory_job=job,minimum_claim_bytes=64*P.GIB,physical_fence_bytes=64*P.GIB,
                    ledger=str(ledger),lock=str(self.root/'lock'),legacy_release_bindings={},
                    capture_headroom_bytes=0)
        result=namespace['reserve'](policy,'isolated-declaration',{'pid':os.getpid()},
                                    self.root/'ADMISSION.json')
        self.assertEqual(result['claim_bytes'],64*P.GIB)
        self.assertEqual(json.loads(ledger.read_text())['fixed_claims']['isolated-declaration'],64*P.GIB)


if __name__=='__main__':
    unittest.main()
