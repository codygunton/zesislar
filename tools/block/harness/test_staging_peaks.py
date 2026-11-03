"""Nonproof controls for dedicated preparation and staging leaves."""
from copy import deepcopy
import json
import os
from pathlib import Path
import signal
import sys
import unittest
from unittest.mock import patch

import admission_memory as M
import staging_peaks as P
import role_peaks
from entry_chain import binding, save
import test_role_peaks
import test_early_canonical_aggregate
import test_proof_cache_key


class TransportWorkload(unittest.TestCase):
    def setUp(self):
        fixture = test_proof_cache_key.ProofCacheKeyTests()
        fixture.setUp()
        self.addCleanup(fixture.doCleanups)
        self.fixture = fixture
        self.output = fixture.work
        self.child = self.output/'CHILD.json'
        save(self.child, fixture.spec)
        self.spec = deepcopy(fixture.spec)
        self.spec['files'].append(dict(binding(self.child), id='child',
                                       kind='configuration', root_role='workspace'))
        self.spec['recipe']['dependencies'].append({'id': 'child', 'requires': []})
        self.input = self.output/'INPUTS.json'
        save(self.input, self.spec)

    def configuration(self, output, reference):
        return {'runtime_path': str(output/'RUNTIME.json'), 'binding_inventory': reference}

    def material(self, output=None, reference=None):
        output = output or self.output
        return P.input_workload(P.ROLES[1], [],
            self.configuration(output, reference or binding(self.input)),
            {'phase': 'prerequisites', 'output': str(output/'jobs/prerequisites')})

    def test_nested_typed_transports_relocate_after_authentication(self):
        import shutil
        before = self.material()
        other = self.fixture.root/'second'
        shutil.copytree(self.output, other)
        child = json.loads((other/'CHILD.json').read_text().replace(str(self.output), str(other)))
        save(other/'CHILD.json', child)
        parent = json.loads(self.input.read_text().replace(str(self.output), str(other)))
        next(row for row in parent['files'] if row['id'] == 'child').update(binding(other/'CHILD.json'))
        save(other/'INPUTS.json', parent)
        self.assertNotEqual(binding(self.input)['sha256'], binding(other/'INPUTS.json')['sha256'])
        self.assertEqual(before, self.material(other, binding(other/'INPUTS.json')))

    def test_nested_digest_tampering_refuses(self):
        self.child.write_text(self.child.read_text() + '\n')
        with self.assertRaises(ValueError):
            self.material()

    def test_changed_source_and_literal_inputs_keep_distinct_identities(self):
        before = self.material()
        self.spec['recipe']['backend']['tactics'].append('idtac "changed".')
        save(self.input, self.spec)
        self.assertNotEqual(before, self.material())
        before = self.material()
        self.spec['recipe']['configuration']['argv'].append(
            {'kind': 'literal', 'value': str(self.output/'literal-text')})
        save(self.input, self.spec)
        self.assertNotEqual(before, self.material())

    def test_changed_source_bytes_cannot_reuse_the_workload(self):
        before = self.material()
        source = self.output/'Proof.v'
        source.write_text(source.read_text() + '(* changed source *)\n')
        child = json.loads(self.child.read_text())
        for document in (child, self.spec):
            next(row for row in document['files'] if row['id'] == 'Proof.v').update(binding(source))
        save(self.child, child)
        next(row for row in self.spec['files'] if row['id'] == 'child').update(binding(self.child))
        save(self.input, self.spec)
        self.assertNotEqual(before, self.material())

    def test_external_bindings_remain_byte_exact(self):
        external = self.fixture.root/'EXTERNAL.json'
        save(external, self.fixture.spec)
        before = self.material(reference=binding(external))
        external.write_text(external.read_text() + '\n')
        self.assertNotEqual(before, self.material(reference=binding(external)))

    def test_undeclared_metadata_path_is_material(self):
        self.spec['recipe']['backend']['features']['material_path'] = str(self.output/'first')
        save(self.input, self.spec)
        before = self.material()
        self.spec['recipe']['backend']['features']['material_path'] = str(self.output/'second')
        save(self.input, self.spec)
        self.assertNotEqual(before, self.material())

    def test_malformed_recognized_schema_stays_refused(self):
        self.spec['recipe']['backend']['features']['material_path'] = {'path': str(self.output)}
        save(self.input, self.spec)
        with self.assertRaisesRegex(ValueError, 'backend feature'):
            self.material()

    def test_unknown_output_schema_disables_historical_sizing(self):
        save(self.input, {'schema': 'unknown.v1', 'path': str(self.output)})
        self.assertIsNone(self.material())

    def test_semantic_projection_keeps_statement_bytes_exact(self):
        projection = {'schema': 'entry-chain.runtime-semantic-projection.v1',
            'provider_fields': {}, 'scope_roles': [], 'phase': 'native', 'module': 'Test.Proof',
            'proof_source_sha256': 'a'*64, 'statement_sha256': 'b'*64}
        save(self.input, projection)
        before = self.material()
        projection['statement_sha256'] = 'c'*64
        save(self.input, projection)
        self.assertNotEqual(before, self.material())


class StagingPeaks(unittest.TestCase):
    def setUp(self):
        old=test_role_peaks.RolePeaks();old.setUp();self.addCleanup(old.doCleanups)
        self.f=old.f;self.payload=old.payload;f=self.f
        self.harness=old.runtime['harness'];root=Path(self.harness['root'])
        for name in ('scratch.py','command_scope.py','code/staging_peaks.py'):
            path=root/'tools/block/harness'/name;path.write_text('# fixture '+name)
        for relative in ('tools/module_memory.py','tools/resource_guard.sh','tools/block/harness/runtime-tools/resource_guard.sh'):
            path=root/relative;path.parent.mkdir(parents=True,exist_ok=True);path.write_text('# fixture '+relative)
        self.command=[sys.executable,'-B',str(root/'tools/block/harness/scratch.py'),
            '--prepare-only','--declarations-only','--harness-commit','fixture','--output','/first/output']
        with patch.object(P,'last_peak',return_value=None),patch.object(P,'identity',return_value=f.owner):
            self.reference,self.value,self.env=P.create(P.ROLES[0],self.harness,self.command,M.GIB,64*M.GIB,
                environment={'ZESU_CANONICAL_LEDGER':str(f.ledger)})
        f.argv=['bash',str(f.guard),'scope-exec',str(f.marker),'--',*self.command]
        f.process(f.actor,14,f.argv,str(f.leaf.relative_to(f.reader.root)))
        M.mark_shell(f.marker,ledger=f.ledger,reader=f.reader);f.post_exec()
        import run_registry as registry
        self.store=f.root/'registry'
        self.run_id='staging-fixture'
        self.registry=registry.Registry(self.store)
        self.registry_row={'id':self.run_id,'owner':'fixture','scheduler':f.owner,
            'jobs':[f.actor,self.payload],'claims':{},'status':'running','exit_code':None,'all_actors_closed':False}
        self.registry.write({'schema':'zesu.run-registry.v1','runs':{self.run_id:self.registry_row}})
        self.env.update(ZESU_RUN_ID=self.run_id)
        registry_store=patch('run_registry.default_store',return_value=self.store);registry_store.start();self.addCleanup(registry_store.stop)
        pin=patch('harness_commit.check');pin.start();self.addCleanup(pin.stop)

    def begin(self):
        with patch.object(P,'identity',return_value=self.f.actor):
            return P.begin(self.f.marker,self.command,ledger=self.f.ledger,reader=self.f.reader,environment=self.env)

    def close(self,code=0):
        f=self.f;reference=role_peaks.finish(self.begin(),self.payload,code)
        data=json.loads(f.ledger.read_text());key=M.shell_key(f.marker)
        data['fixed_claims'][key]=0;data['shell_releases']={key:{'owner':f.owner,'marker':str(f.marker)}}
        f.ledger.write_text(json.dumps(data));f.marker.unlink()
        for actor in (f.owner,f.actor):
            path=f.proc/str(actor['pid'])/'stat';path.write_text(path.read_text().replace('(process) S','(process) Z'))
        for path in f.leaf.iterdir():path.unlink()
        f.leaf.rmdir()
        self.registry_row.update(status='completed'if code==0 else 'failed',exit_code=code,all_actors_closed=True)
        self.registry.write({'schema':'zesu.run-registry.v1','runs':{self.run_id:self.registry_row}})
        return reference

    def latest(self,role=None,kind=None,source=None):
        return P.last_peak(role or P.ROLES[0],kind or self.value['run_kind'],source or (self.value['workload'],self.value['input_workload']),
            ledger=self.f.ledger,reader=self.f.reader)

    def test_exact_leaf_normal_nonzero_exit_and_release(self):
        reference=self.close(7)
        self.assertEqual(self.latest(),(reference,3*M.GIB))
        value=json.loads(Path(reference['path']).read_text())
        self.assertEqual(value['scope']['scope'],str(self.f.leaf))
        self.assertNotEqual(value['scope']['scope'],str(self.f.group))
        self.assertEqual(value['returncode'],7)

    def test_live_actors_unreleased_claim_and_existing_leaf_refuse(self):
        reference=role_peaks.finish(self.begin(),self.payload,0)
        self.assertIsNone(self.latest())
        with self.assertRaisesRegex(ValueError,'closed and released'):
            P.recorded(reference,P.ROLES[0],self.value['run_kind'],(self.value['workload'],self.value['input_workload']),
                ledger=self.f.ledger,reader=self.f.reader)

    def test_wrong_role_kind_source_and_missing_evidence_keep_default(self):
        self.close()
        for arguments in ({'role':P.ROLES[1]},{'kind':'prepare-native'},{'source':'changed'}):
            self.assertIsNone(self.latest(**arguments))
        self.f.ledger.write_text('{}');self.assertIsNone(self.latest())

    def test_interrupted_exit_is_recorded_but_not_reused(self):
        reference=self.close(-signal.SIGTERM)
        self.assertEqual(json.loads(Path(reference['path']).read_text())['returncode'],-signal.SIGTERM)
        self.assertIsNone(self.latest())

    def test_changed_owner_release_or_claim_refuses(self):
        self.close();original=self.f.ledger.read_text();key=M.shell_key(self.f.marker)
        for field in ('release','owner','claim'):
            value=json.loads(original)
            if field=='release':value['shell_releases'][key]['marker']='changed'
            elif field=='owner':value['shell_claim_owners'][key]['owner']['startticks']+=1
            else:value['fixed_claims'][key]=1
            self.f.ledger.write_text(json.dumps(value));self.assertIsNone(self.latest())

    def test_changed_source_or_command_refuses_before_execution(self):
        path=Path(self.harness['root'])/'tools/block/harness/scratch.py';original=path.read_bytes()
        path.write_text('# changed')
        with self.assertRaisesRegex(ValueError,'workload source'):self.begin()
        path.write_bytes(original);self.command.append('--run')
        with self.assertRaisesRegex(ValueError,'payload or claim'):self.begin()

    def test_parent_backstop_cannot_replace_leaf_fence(self):
        (self.f.leaf/'memory.max').write_text('max')
        with self.assertRaises(ValueError):self.begin()

    def test_metadata_refresh_and_proof_execution_are_not_preparation(self):
        for arguments in (['--run','a','b','--prepare-only'],['--refresh-memory','--prepare-only'],[],['--help']):
            with self.assertRaises(ValueError):P.run_kind(P.ROLES[0],arguments)
        self.assertEqual(P.run_kind(P.ROLES[0],['--prepare-only']),'prepare-native')
        with self.assertRaises(ValueError):P.run_kind('entry-pilot-mcp',['--prepare-only'])

    def test_changed_output_preserves_historical_workload_identity(self):
        reference=self.close()
        with patch.object(P,'last_peak',return_value=(reference,3*M.GIB))as selection:
            _,value,_=P.create(P.ROLES[0],self.harness,[*self.command[:-1],'/new/output'],M.GIB,64*M.GIB,
                environment={'ZESU_CANONICAL_LEDGER':str(self.f.ledger)})
        selection.assert_called_once_with(P.ROLES[0],self.value['run_kind'],(self.value['workload'],self.value['input_workload']))
        self.assertEqual(value['claim_bytes'],9*M.GIB//2)
        self.assertEqual(value['command'][-1],'/new/output')
        self.assertEqual(value['selected_peak'],reference)

    def test_missing_peak_keeps_booking_and_clears_inherited_authority(self):
        with patch.object(P,'last_peak',return_value=None):
            _,value,environment=P.create(P.ROLES[0],self.harness,self.command,24*M.GIB,64*M.GIB,
                environment={'ZESU_CANONICAL_LEDGER':str(self.f.ledger),'ZESU_CONTROLLER_ROLE':'entry-chain-client',
                    'ZESU_COQC_SCOPE':'old token','ZESU_OWNED_GUARD_TOKEN':'old marker'})
        self.assertEqual(value['claim_bytes'],24*M.GIB)
        for key in ('ZESU_CONTROLLER_ROLE','ZESU_COQC_SCOPE','ZESU_OWNED_GUARD_TOKEN'):
            self.assertNotIn(key,environment)

    def test_physical_environment_resets_staging_authority(self):
        from scope_bookings import reset_controller
        self.assertEqual(reset_controller({P.KEYS[0]:'path',P.KEYS[1]:'hash','unrelated':'kept'}),{'unrelated':'kept'})

    def test_owned_staging_binds_exact_job_configuration(self):
        config={'harness':self.harness,'jobs':[{'key':'prerequisites','phase':'prerequisites',
            'output':str(self.f.out),'claim_bytes':24*M.GIB,'physical_fence_bytes':64*M.GIB}]}
        path=self.f.root/'CONFIG.json';save(path,config)
        job=dict(config['jobs'][0],policy={'minimum_claim_bytes':24*M.GIB})
        command=[sys.executable,'-B',str(Path(self.harness['root'])/'tools/block/harness/code/staging_peaks.py'),'--execute']
        with patch.object(P,'last_peak',return_value=None):
            reference,value,_=P.create(P.ROLES[1],self.harness,command,24*M.GIB,64*M.GIB,
                job=job,configuration=binding(path),output=str(self.f.out),
                environment={'ZESU_CANONICAL_LEDGER':str(self.f.ledger)})
        self.assertEqual(P.context(reference,self.f.reader)['run_kind'],'staging-prerequisites-serial')
        config['jobs'][0]['claim_bytes']=8*M.GIB;save(path,config)
        with self.assertRaises(ValueError):P.context(reference,self.f.reader)

    def test_changed_material_input_cannot_reuse_previous_peak(self):
        source=self.f.root/'Entry.v';source.write_text('Definition entry := 1.')
        first=P.input_workload(P.ROLES[0],[*self.command,str(source)])
        source.write_text('Definition entry := 2.')
        second=P.input_workload(P.ROLES[0],[*self.command,str(source)])
        self.assertNotEqual(first,second)
        config={'runtime_path':'/old/output/RUNTIME.json','jobs':[{'output':'/old/output/jobs/prerequisites','ordered_modules':['A']}],
            'physical_flags':['-Q','/old/output/workspace','Project'],'object_imports':{'A':{'path':'/inputs/OBJECT.json','sha256':'first'}}}
        job={'output':'/old/output/jobs/prerequisites','phase':'prerequisites'}
        old=P.input_workload(P.ROLES[1],[],config,job)
        relocated=json.loads(json.dumps(config).replace('/old/output','/new/output'))
        relocated_job=json.loads(json.dumps(job).replace('/old/output','/new/output'))
        self.assertEqual(old,P.input_workload(P.ROLES[1],[],relocated,relocated_job))
        relocated['object_imports']['A']['sha256']='changed'
        self.assertNotEqual(old,P.input_workload(P.ROLES[1],[],relocated,relocated_job))

    def test_exact_runtime_hash_overlay_is_allowed_and_other_changes_refuse(self):
        path=self.f.root/'PUBLIC-RUNTIME.json';save(path,{'jobs':[]})
        reference=binding(path)
        expected={'jobs':[],'runtime_path':reference['path'],'runtime_sha256':reference['sha256']}
        self.assertEqual(P.configuration_value(reference,{key:expected[key]for key in ('runtime_path','runtime_sha256')}),expected)
        for overlay in ({'runtime_sha256':'changed'},{'runtime_path':'/other/RUNTIME.json'},{'control_session':'extra'}):
            with self.assertRaises(ValueError):P.configuration_value(reference,overlay)

    def test_actual_stock_staging_constructor_accepts_bound_runtime_metadata(self):
        import ast
        from contextlib import nullcontext
        import entry_chain_run
        from types import SimpleNamespace
        config={'harness':self.harness,'jobs':[{'key':'block','phase':'prerequisites',
            'output':str(self.f.out),'claim_bytes':24*M.GIB,'physical_fence_bytes':64*M.GIB}]}
        path=self.f.root/'STOCK-RUNTIME.json';save(path,config)
        config.update(runtime_path=str(path),runtime_sha256=binding(path)['sha256'])
        job=dict(config['jobs'][0],policy={'claim_key':'fixed-root'})
        staged=self.f.out/'RUNTIME.json';save(staged,{'prepared_workspace':str(self.f.root/'workspace')})
        save(self.f.out/'STARTED.json',{'owner':{'pid':os.getpid(),'startticks':P.identity(os.getpid())['startticks']}})
        # Execute the actual stock boundary statement, including its real stage constructor.
        tree=ast.parse(Path(entry_chain_run.__file__).read_text())
        function=next(node for node in tree.body if isinstance(node,ast.FunctionDef)and node.name=='run_stock_job')
        boundary=next(node for node in ast.walk(function)if isinstance(node,ast.With)
            and any(isinstance(call,ast.Call)and any(isinstance(arg,ast.Constant)and arg.value=='owned_staging'for arg in call.args)for call in ast.walk(node.items[0].context_expr)))
        selected=[]
        def launched(argv,**kwargs):
            selected.append((argv,kwargs))
            return SimpleNamespace(pid=os.getpid(),wait=lambda:0)
        namespace={'attribution':SimpleNamespace(span=lambda name:nullcontext()),'prepared':None,
            'config':config,'job':job,'out':self.f.out}
        with patch.object(P,'last_peak',return_value=None),patch('controller_cleanup.launch',side_effect=launched),patch('memory_policy.environment',return_value={}):
            exec(compile(ast.Module(body=[boundary],type_ignores=[]),'actual-stock-staging','exec'),namespace)
        self.assertEqual(namespace['workspace'],self.f.root/'workspace')
        reference={'path':selected[0][1]['env'][P.KEYS[0]],'sha256':selected[0][1]['env'][P.KEYS[1]]}
        context=P.context(reference,self.f.reader)
        self.assertEqual(context['derived_configuration'],{'runtime_path':str(path),'runtime_sha256':binding(path)['sha256']})
        self.assertEqual(context['role'],P.ROLES[1])
        changed=dict(config,control_session={'unexpected':True})
        with self.assertRaisesRegex(ValueError,'differs from its public runtime'):
            P.stage(changed,job,self.f.out)

    def test_malformed_peak_rows_keep_default(self):
        self.close();original=self.f.ledger.read_text()
        for row in (None,3,[],{'role':P.ROLES[0],'run_kind':self.value['run_kind'],'receipt':{'path':'/missing','sha256':'bad'}}):
            data=json.loads(original);data['controller_exit_peaks']=[row]
            self.f.ledger.write_text(json.dumps(data));self.assertIsNone(self.latest())

    def test_revision_metadata_does_not_hide_material_input_changes(self):
        config={'runtime_path':'/old/output/RUNTIME.json','harness':{'root':'/pin/old','commit':'old','tree':'old','tools_tree':'old'},
            'job_controller':{'path':'/pin/old/tools/controller.py','sha256':'same'},'ordered_modules':['A'],
            'physical_flags':['-Q','/old/output/workspace','Project']}
        job={'output':'/old/output/jobs/prerequisites','phase':'prerequisites'}
        original=P.input_workload(P.ROLES[1],[],config,job)
        changed=deepcopy(config);changed['harness'].update(root='/pin/new',commit='new',tree='new',tools_tree='new')
        changed['job_controller']['path']='/pin/new/tools/controller.py'
        self.assertEqual(original,P.input_workload(P.ROLES[1],[],changed,job))
        changed['ordered_modules'].append('B')
        self.assertNotEqual(original,P.input_workload(P.ROLES[1],[],changed,job))


    def test_registry_identity_live_actor_and_claim_refuse(self):
        self.close();original=deepcopy(self.registry_row)
        for mutation in ('scheduler','owner','actor','claim','status'):
            row=deepcopy(original)
            if mutation=='scheduler':row['scheduler']['startticks']+=1
            elif mutation=='owner':row['owner']='another owner'
            elif mutation=='actor':
                actor={'pid':17,'startticks':107};self.f.process(actor,1,['live actor'],'/outside');row['jobs'].append(actor)
            elif mutation=='claim':row['claims']['held']={'released':False}
            else:row['status']='stopped'
            self.registry.write({'schema':'zesu.run-registry.v1','runs':{self.run_id:row}})
            self.assertIsNone(self.latest())

    def test_unrecognized_transport_cannot_select_a_historical_peak(self):
        with patch.object(P, 'input_workload', return_value=None), \
                patch.object(P, 'last_peak', side_effect=AssertionError('Unknown transport reused')):
            _, value, _ = P.create(P.ROLES[0], self.harness, self.command, 24*M.GIB, 64*M.GIB,
                environment={'ZESU_CANONICAL_LEDGER': str(self.f.ledger)})
        self.assertEqual(value['claim_bytes'], 24*M.GIB)
        self.assertIsNone(value['selected_peak'])

    def test_outer_preparation_helper_change_changes_workload(self):
        root = Path(self.harness['root'])
        helper = root/'tools/block/entry_bindings.py'
        helper.write_text('# original preparation helper\n')
        before = P.workload(root)
        helper.write_text('# changed preparation helper\n')
        self.assertNotEqual(before, P.workload(root))


class EarlyStaging(unittest.TestCase):
    def setUp(self):
        f=test_early_canonical_aggregate.EarlyCanonicalAggregate();f.setUp()
        self.addCleanup(f.doCleanups);self.f=f
        root=f.guard.parents[1];harness={'root':str(root),'commit':'fixture'}
        for name in ('scratch.py','command_scope.py','code/staging_peaks.py','code/entry_chain_run.py'):
            path=root/'tools/block/harness'/name;path.parent.mkdir(parents=True,exist_ok=True);path.write_text('# fixture '+name)
        for relative in ('tools/module_memory.py','tools/block/harness/runtime-tools/resource_guard.sh'):
            path=root/relative;path.parent.mkdir(parents=True,exist_ok=True);path.write_text('# fixture '+relative)
        controller=root/'tools/block/harness/code/entry_chain_run.py'
        config={'harness':harness,'jobs':[{'key':'block','output':str(f.out),
            'phase':'prerequisites','claim_bytes':64*M.GIB,'physical_fence_bytes':64*M.GIB}]}
        config_path=f.root/'CONFIG.json';save(config_path,config)
        command=[sys.executable,'-B',str(root/'tools/block/harness/code/staging_peaks.py'),'--execute']
        with patch.object(P,'last_peak',return_value=None),patch.object(P,'identity',return_value={k:f.owner[k]for k in ('pid','startticks')}):
            self.reference,self.value,_=P.create(P.ROLES[1],harness,command,64*M.GIB,64*M.GIB,
                job=dict(config['jobs'][0],policy={'claim_key':f.key}),configuration=binding(config_path),
                output=str(f.out),environment={'ZESU_CANONICAL_LEDGER':str(f.ledger)},canonical_root=f.owner)
        f.command=[str(f.guard),'batch','entry-staging-block','--',str(f.guard),'scope',
            'owned-staging','--cpu','unlimited','--',*P.payload(self.reference,self.value)]
        f.wrapper=['python3','-B',str(f.guard.with_name('run_registry.py')),'run','--kind','stock-batch',
            '--owner','fixture','--',*f.command]
        f.process(f.owner,1,['python','-B',str(controller),str(config_path),binding(config_path)['sha256'],'block',str(f.out)],'/outside')
        f.process(f.batch,11,f.wrapper,'/outside')
        f.process(f.creator,12,['bash',*f.command],'/outside')
        f.process(f.pending,15,['bash',*f.command[4:]],str(f.group.relative_to(f.reader.root)))
        (f.out/'LAUNCH.json').unlink()
        (f.out/'BATCH-PROCESS.json').rename(f.out/'STAGING-PROCESS.json')
        f.write(f.out/'STAGING-LAUNCH.json',{'owner':f.owner,'argv':f.command,'context':self.reference})

    def test_actual_pending_token_authenticates_staging_root(self):
        f=self.f;value=f.reader.claim(f.data,f.key,pending_shell=(f.marker,f.token))
        self.assertTrue(value['verified'],value)
        self.assertEqual(value['scope'],str(f.group))

    def test_wrong_role_or_source_refuses_root_association(self):
        f=self.f
        path=Path(self.reference['path']);value=json.loads(path.read_text());value['role']='entry-pilot-mcp'
        path.write_text(json.dumps(value));f.write(f.out/'STAGING-LAUNCH.json',{'owner':f.owner,'argv':f.command,'context':binding(path)})
        self.assertFalse(f.reader.claim(f.data,f.key,pending_shell=(f.marker,f.token))['verified'])

    def test_changed_owner_and_configuration_refuse(self):
        f=self.f;original=Path(self.reference['path']).read_text()
        for field in ('owner','configuration'):
            value=json.loads(original)
            if field=='owner':value['owner']['startticks']+=1
            else:value['configuration']['sha256']='changed'
            Path(self.reference['path']).write_text(json.dumps(value))
            f.write(f.out/'STAGING-LAUNCH.json',{'owner':f.owner,'argv':f.command,'context':binding(Path(self.reference['path']))})
            self.assertFalse(f.reader.claim(f.data,f.key,pending_shell=(f.marker,f.token))['verified'])


if __name__=='__main__':unittest.main()
