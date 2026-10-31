"""Nonproof controls for the frozen declaration-wave dispatcher."""
from concurrent.futures import ThreadPoolExecutor
from copy import deepcopy
from pathlib import Path
from types import SimpleNamespace
from unittest.mock import patch
from contextlib import asynccontextmanager
import ast
import asyncio
import hashlib
import json
import subprocess
import sys
import tempfile
import threading
import time
import unittest

HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE/'code'))
import dependency_batch as D


class DependencyBatchTests(unittest.TestCase):
    def setUp(self):
        self.temporary=tempfile.TemporaryDirectory(dir=HERE.parent)
        self.addCleanup(self.temporary.cleanup)
        self.root=Path(self.temporary.name)
        self.workspace=self.root/'workspace';self.workspace.mkdir()
        self.output=self.root/'output';self.output.mkdir()
        self.plan=json.loads(Path(D.AUTHORITY['path']).read_text())
        self.real_manifest=D.read_bound(self.plan['source_boundary'])
        self.modules={}
        for index,row in enumerate(self.plan['modules']):
            source=self.workspace/(row['module'].replace('.','/')+'.v')
            source.parent.mkdir(parents=True,exist_ok=True)
            source.write_text('Definition support_'+str(index)+' := 0.\n')
            source.with_suffix('.vo').write_bytes(b'old object')
            self.modules[row['module']]=str(source.relative_to(self.workspace))
            row['source']=D.binding(source)
        manifest={'source_rows':[]}
        for name in self.plan['MCP_only_libraries']:
            source=self.workspace/(name.replace('.','/')+'.v')
            source.parent.mkdir(parents=True,exist_ok=True)
            source.write_text('Definition protected := 0.\n');source.with_suffix('.vo').write_bytes(b'compiled barrier')
            self.modules[name]=str(source.relative_to(self.workspace))
            manifest['source_rows'].append(dict(module=name,**D.binding(source)))
        path=self.root/'source.json';D.save(path,manifest);self.plan['source_boundary']=D.binding(path)
        tool_paths={'guard':'tools/resource_guard.sh','compile_measure_helper':'tools/block/dependency_compile_measure.py',
                    'run_registry':'tools/run_registry.py','compiler':'compiler','dune':'dune'}
        for key,relative in tool_paths.items():
            target=self.workspace/relative;target.parent.mkdir(parents=True,exist_ok=True)
            target.write_text('bound tool '+key);self.plan[key]=D.binding(target)
        self.plan['parallelism']['maximum_workers']=2
        self.graph={'import_edges':deepcopy(self.plan['dependency_edges'])}
        path=self.root/'graph.json';D.save(path,self.graph);self.graph_binding=D.binding(path)
        path=self.root/'plan.json';D.save(path,self.plan);self.authority=D.binding(path)
        self.patch=patch.object(D,'AUTHORITY',self.authority);self.patch.start();self.addCleanup(self.patch.stop)
        self.ordered=['ZesuSsz.Automation.Hooks',*self.plan['waves'][0]['modules'],
                      'ZesuSsz.Automation.Finish','ZesuSsz.Automation.All',*self.plan['waves'][1]['modules']]
        self.runtime={'phase':'prerequisites','physical_flags':['-q','-R',str(self.workspace),'ZesuSsz'],
            'module_files':self.modules,'build_dir':'artifacts',
            'canonical_admission':{'minimum_claim_bytes':24*D.GIB,'physical_fence_bytes':64*D.GIB}}
        self.spec={'plan':self.authority,'graph':self.graph_binding,'declarations_only':True,
                   'flags_sha256':D.fingerprint(self.runtime['physical_flags'],self.workspace)}
        self.runtime['dependency_batch']=self.spec

    def validate(self):
        return D.validate(self.runtime,self.workspace,self.ordered,self.spec)

    def test_valid_exact_plan(self):
        self.assertEqual(len(self.validate()[0]['modules']),23)

    def test_actual_restart_staging_installs_the_exact_recorder(self):
        import restart_bindings
        owned=self.root/'staged';owned.mkdir()
        config={'admission':{},'harness':{'commit':'fixture'}}
        with patch('harness_commit.check'):
            result=restart_bindings.install_restart_tools(owned,config,HERE)
        staged=owned/'tools/block/dependency_compile_measure.py'
        self.assertEqual(D.binding(staged)['sha256'],
            'bb54ce6bc73f6841ce2caeb53dfb8c0e3d6dd1eb782bb4f166ab1a8d3a5ea609')
        source=HERE/'runtime-tools/block/dependency_compile_measure.py'
        matches=[row for row in result['copies'] if row['owned']['path']==str(staged)]
        self.assertEqual(len(matches),1)
        self.assertEqual(matches[0]['source'],D.binding(source))
        self.assertTrue(matches[0]['distinct_inode'])

    def test_native_phase_refuses(self):
        self.runtime['phase']='native'
        with self.assertRaisesRegex(ValueError,'prerequisite'):self.validate()

    def test_missing_declaration_mode_refuses(self):
        self.spec['declarations_only']=False
        with self.assertRaises(ValueError):self.validate()

    def test_changed_claim_or_fence_refuses(self):
        for key in ['minimum_claim_bytes','physical_fence_bytes']:
            old=self.runtime['canonical_admission'][key]
            self.runtime['canonical_admission'][key]=8*D.GIB
            with self.assertRaises(ValueError):self.validate()
            self.runtime['canonical_admission'][key]=old

    def test_minimal_or_interactive_route_refuses(self):
        for key in ['native_route','control_session']:
            self.runtime[key]={'unexpected':True}
            with self.assertRaises(ValueError):self.validate()
            del self.runtime[key]

    def test_changed_source_refuses(self):
        Path(self.plan['modules'][0]['source']['path']).write_text('changed')
        with self.assertRaisesRegex(ValueError,'source changed'):self.validate()

    def test_changed_mcp_library_refuses(self):
        source=self.workspace/self.modules['ZesuSsz.Automation.Hooks'];source.write_text('changed')
        with self.assertRaisesRegex(ValueError,'MCP library'):self.validate()

    def test_flags_refuse(self):
        self.runtime['physical_flags'].append('-noinit')
        with self.assertRaisesRegex(ValueError,'flags'):self.validate()

    def test_guard_refuses(self):
        (self.workspace/'tools/resource_guard.sh').write_text('different guard')
        with self.assertRaises(ValueError):self.validate()

    def test_source_escape_refuses(self):
        outside=self.root/'outside.v';outside.write_bytes(Path(self.plan['modules'][0]['source']['path']).read_bytes())
        self.runtime['module_files'][self.plan['modules'][0]['module']]=str(outside)
        with self.assertRaises(ValueError):self.validate()

    def test_unauthorized_plan_refuses(self):
        self.spec['plan']=dict(self.authority,sha256='0'*64)
        with self.assertRaisesRegex(ValueError,'authorized'):self.validate()

    def test_barrier_order_refuses(self):
        self.ordered.remove('ZesuSsz.Automation.Finish');self.ordered.insert(1,'ZesuSsz.Automation.Finish')
        with self.assertRaisesRegex(ValueError,'barrier'):self.validate()

    def test_internal_order_refuses(self):
        for edge in self.graph['import_edges']:
            if edge['from'] in self.plan['waves'][0]['modules'] and edge['to'] in self.plan['waves'][0]['modules']:
                self.ordered.remove(edge['to']);self.ordered.insert(self.ordered.index(edge['from'])+1,edge['to']);break
        with self.assertRaisesRegex(ValueError,'topological'):self.validate()

    def test_changed_edges_refuse(self):
        self.graph['import_edges'].append({'from':self.plan['modules'][0]['module'],'to':'ZesuSsz.Automation.All'})
        path=Path(self.graph_binding['path']);D.save(path,self.graph);self.spec['graph']=D.binding(path)
        with self.assertRaisesRegex(ValueError,'edges changed'):self.validate()

    def test_native_preparation_drops_execution_but_keeps_lineage(self):
        config={'dependency_batch':deepcopy(self.spec),'proof_runtime':{'dependency_batch':deepcopy(self.spec)},
                'bindings':[self.authority, self.graph_binding]}
        before=deepcopy(config['bindings']);transition=D.inherit(config)
        self.assertNotIn('dependency_batch',config)
        self.assertNotIn('dependency_batch',config['proof_runtime'])
        self.assertEqual(config['bindings'],before)
        self.assertEqual(transition['removed']['plan'],self.authority)
        self.assertFalse(transition['native_replay_enabled'])

    def test_actual_native_preparation_records_the_drop_before_staging(self):
        import scratch
        config={'dependency_batch':deepcopy(self.spec),'proof_runtime':{'dependency_batch':deepcopy(self.spec)},
                'bindings':[self.authority]}
        base=self.root/'ready.json';D.save(base,config)
        output=self.root/'native-prepare'
        args=SimpleNamespace(harness_commit='0'*40,supplier_controls=None,output=output,base_runtime=base,
            base_runtime_sha256=D.binding(base)['sha256'],seed_reference=None,
            dependency_cache=None,declarations_only=False)
        with patch('harness_commit.pin',return_value={'commit':'fixture'}),patch.object(scratch,'read_bound',return_value=config):
            with self.assertRaises(KeyError):scratch.prepare(args)
        transition=json.loads((output/'DECLARATION-WAVE-TRANSITION.json').read_text())
        self.assertEqual(transition['removed']['plan'],self.authority)
        self.assertTrue(transition['lineage_retained'])
        self.assertEqual(config['bindings'],[self.authority])
        self.assertNotIn('dependency_batch',config['proof_runtime'])

    def test_stage_only_passes_wave_metadata_to_prerequisites(self):
        config={'dependency_batch':self.spec,'declarations_only':True}
        self.assertIs(D.for_phase(config,'prerequisites'),self.spec)
        with self.assertRaisesRegex(ValueError,'native staging'):D.for_phase(config,'native')
        config['declarations_only']=False
        with self.assertRaises(ValueError):D.for_phase(config,'prerequisites')
        self.assertIsNone(D.for_phase({},'native'))

    def test_provider_rejects_native_before_proof_environment(self):
        import entry_chain_provider as provider
        with patch.object(provider,'bound_json',return_value={'phase':'native','dependency_batch':self.spec}),patch.object(provider,'proof_environment') as environment:
            with self.assertRaisesRegex(ValueError,'native phase'):
                asyncio.run(provider.execute({'runtime':'unused','runtime_sha256':'unused'}))
        environment.assert_not_called()

    def test_actual_provider_skips_wave_modules_after_completion(self):
        import entry_chain_provider as provider
        members=self.plan['waves'][0]['modules']
        runtime=dict(self.runtime,target={},ordered_modules=members,mcp_argv=['nonproof-fixture'])
        tool_calls=[];waves=[]
        class Session:
            async def __aenter__(self):return self
            async def __aexit__(self,*args):pass
            async def initialize(self):pass
            async def call_tool(self,name,arguments):
                tool_calls.append(name)
                return SimpleNamespace(structuredContent={'success':True},isError=False,
                    model_dump=lambda **kwargs:{})
        @asynccontextmanager
        async def streams(*args,**kwargs):yield (None,None)
        def wave(index,runtime,workspace,output,ordered,completed,environment,**kwargs):
            waves.append(index);completed.update(members);return {}
        with patch.object(provider,'bound_json',return_value=runtime),patch.object(provider,'check_proof_bindings'),patch.object(provider,'check_operation',return_value={}),patch.object(provider,'proof_environment',return_value={}),patch.object(provider,'stdio_client',streams),patch.object(provider,'ClientSession',return_value=Session()),patch.object(D,'run_wave',side_effect=wave):
            asyncio.run(provider.execute({'runtime':'nonproof','runtime_sha256':'unused',
                'workspace':str(self.workspace),'output':str(self.output),'identity':{}}))
        self.assertEqual(waves,[0])
        self.assertEqual(tool_calls,['rocq_health','rocq_health'])

    def test_worker_budget_uses_memory(self):
        self.assertEqual(D.worker_limit(self.plan,64*D.GIB),2)
        with self.assertRaises(ValueError):D.worker_limit(self.plan,1)

    def fake_compile(self,module,*args):
        return {'result':{'success':True}}

    def run_wave(self,compile_one):
        with patch.object(D,'compile_one',side_effect=compile_one),patch.object(D.subprocess,'run',return_value=SimpleNamespace(stdout='2\n')):
            completed=set()
            result=D.run_wave(0,self.runtime,self.workspace,self.output,self.ordered,completed,{})
            return result,completed

    def test_real_scheduler_obeys_internal_dependencies(self):
        seen=set();lock=threading.Lock();members=set(self.plan['waves'][0]['modules'])
        def compile_one(module,*args):
            deps={row['to'] for row in self.graph['import_edges'] if row['from']==module and row['to'] in members}
            with lock:self.assertTrue(deps<=seen)
            time.sleep(.01)
            with lock:seen.add(module)
            return {'result':{'success':True}}
        result,completed=self.run_wave(compile_one)
        self.assertEqual(set(result),members);self.assertEqual(completed,members)

    def test_failure_stops_new_work_and_finishes_healthy_children(self):
        started=[];healthy=threading.Event();failed=threading.Event();lock=threading.Lock()
        def compile_one(module,*args):
            with lock:started.append(module);index=len(started)
            if index==1:
                healthy.wait(1);failed.set();raise RuntimeError('planted failure')
            healthy.set();failed.wait(1);time.sleep(.03)
            return {'result':{'success':True}}
        with self.assertRaisesRegex(RuntimeError,'later dispatch stopped'):self.run_wave(compile_one)
        self.assertEqual(len(started),2)
        receipt=json.loads((self.output/'DEPENDENCY-WAVE-0.json').read_text())
        self.assertEqual(len(receipt['completed']),1)
        self.assertTrue(receipt['healthy_children_are_not_stopped'])
        self.assertEqual(len(receipt['active']),0)

    def test_completed_modules_are_not_dispatched_again(self):
        members=set(self.plan['waves'][0]['modules']);completed=set(members)
        with patch.object(D,'compile_one') as compiler,patch.object(D.subprocess,'run',return_value=SimpleNamespace(stdout='2\n')):
            D.run_wave(0,self.runtime,self.workspace,self.output,self.ordered,completed,{})
        compiler.assert_not_called()

    def test_actual_cwd_and_physical_identity_are_checked(self):
        module=self.plan['modules'][0]['module'];record_root=self.workspace/'records';record_root.mkdir()
        def runner(argv,**kwargs):
            record=Path(argv[-1]);source=self.workspace/self.modules[module]
            value=json.loads((record/'INPUT.json').read_text());value['cwd']=str(record)
            D.save(record/'INPUT.json',value)
            source.with_suffix('.vo').write_bytes(b'new object')
            source.with_suffix('.glob').write_text('DIGEST\nF'+module+'\n')
            D.save(record/'PHYSICAL-RESULT.json',{'input':D.binding(record/'INPUT.json'),
                'physical_argv':value['physical_argv'],'returncode':0})
            self.assertEqual(kwargs['cwd'],record)
            self.assertIn('--no-build',argv)
            return SimpleNamespace(returncode=0)
        receipt=D.compile_one(module,self.plan,self.graph,self.runtime,self.workspace,self.output,record_root,{},runner)
        self.assertEqual(receipt['actual_cwd'],str(record_root/module))
        self.assertEqual(receipt['result']['method'],'guarded-dune-dependency-build')
        self.assertEqual(receipt['source_sha256'],self.plan['modules'][0]['source']['sha256'])

    def test_bound_shim_creates_isolated_compiler_directories(self):
        # Execute only the bound Python cwd shim. No Dune or compiler runs.
        script=self.root/'recorder.py'
        script.write_text('import os,pathlib,sys; pathlib.Path(sys.argv[1],"actual").write_text(os.getcwd())\n')
        records=[self.workspace/'first',self.workspace/'second']
        for record in records:record.mkdir()
        def launch(record):
            argv=D.module_command(self.plan,self.runtime,self.workspace,script,record)
            start=argv.index('--')+1
            subprocess.run(argv[start:],cwd=self.workspace,check=True)
        with ThreadPoolExecutor(max_workers=2) as pool:list(pool.map(launch,records))
        for record in records:self.assertEqual((record/'actual').read_text(),str(record))


if __name__=='__main__':
    unittest.main()
