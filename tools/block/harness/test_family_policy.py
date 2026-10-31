from pathlib import Path
from unittest.mock import patch
import ast,copy,hashlib,json,os,subprocess,sys,tempfile,unittest
HERE=Path(__file__).resolve().parent
sys.path[:0]=[str(HERE/'code'),str(HERE.parents[0]),str(HERE.parents[1])]
import memory_policy as P
import scratch_limits as L
def binding(path):return {'path':str(path),'sha256':hashlib.sha256(path.read_bytes()).hexdigest()}
class FamilyPolicyTests(unittest.TestCase):
 def setUp(self):
  self.temp=tempfile.TemporaryDirectory();self.addCleanup(self.temp.cleanup);self.root=Path(self.temp.name)
  self.native=self.root/'Native.v';self.native.write_text('Require Import ZesuSsz.Automation.All.\nLemma body : True. Proof. zesu_block. Qed.\n')
  self.entry=self.root/'Entries.v';self.entry.write_text('Definition pass_entry := True.\n')
  self.rules=self.root/'Rules.v';self.rules.write_text('Require Import ZesuSsz.Generated.DecodeItem.Entries.\n')
  self.recipe=self.root/'REUSE-RECIPE.json';self.recipe.write_text('{}')
  self.modules={'Fixture.Native':'Native.v','ZesuSsz.Generated.DecodeItem.Entries':'Entries.v','Fixture.Rules':'Rules.v'}
  self.config={'prepared_workspace':str(self.root),'proof_runtime':{'module_files':self.modules},'declarations_only':True}
  self.target={'module':'Fixture.Native','source_sha256':binding(self.native)['sha256'],'statement_sha256':'0'*64}
  self.job={'phase':'native','target':self.target}
 def profile(self,focused=False,role='consumer_check'):
  if focused:
   value={'schema':'scratch.admission-profile.v1','kind':'focused_check','sources':[dict(binding(self.rules),module='Fixture.Rules',role=role)]}
  else:
   value={'schema':'scratch.admission-profile.v1','kind':'stock_pass_spec_bundle','native_source':dict(binding(self.native),module='Fixture.Native'),'pass_entries':dict(binding(self.entry),module='ZesuSsz.Generated.DecodeItem.Entries'),'bundle_source':dict(binding(self.rules),module='Fixture.Rules'),'spec_recipe':binding(self.recipe)}
  path=self.root/'profile.json';path.write_text(json.dumps(value));return binding(path)
 def test_unknown_native_keeps64(self):self.assertEqual(P.apply_job(self.job)['claim_bytes'],64*P.GIB)
 def test_source_bound_family_without_own_measurement_uses16(self):
  w=P.workload_for_job(self.profile(),self.job,self.config);j=P.apply_job(self.job,workload=w);self.assertEqual(P.validate_job(j),16*P.GIB);self.assertEqual(j['physical_fence_bytes'],64*P.GIB);self.assertEqual(P.PARENT_FENCE,175*P.GIB)
 def test_family_source_mismatch_refuses(self):
  profile=self.profile();self.native.write_text('changed')
  with self.assertRaises(ValueError):P.workload_for_job(profile,self.job,self.config)
 def test_private_route_refuses(self):
  self.native.write_text(self.native.read_text()+'\nLtac checkpoint := idtac.\n');self.job['target']['source_sha256']=binding(self.native)['sha256']
  with self.assertRaisesRegex(ValueError,'plain stock'):P.workload_for_job(self.profile(),self.job,self.config)
 def test_focus_uses8_with24_fence(self):
  job={'phase':'prerequisites','ordered_modules':['Fixture.Rules']};w=P.workload_for_job(self.profile(True),job,self.config);j=P.apply_job(job,workload=w);self.assertEqual(P.validate_job(j),8*P.GIB);self.assertEqual(j['physical_fence_bytes'],64*P.GIB)
 def test_rule_compilation_keeps24(self):
  job={'phase':'prerequisites','ordered_modules':['Fixture.Rules']};self.assertEqual(P.apply_job(job)['claim_bytes'],24*P.GIB)
  with self.assertRaisesRegex(ValueError,'rule compilation'):P.workload_for_job(self.profile(True,'rule_definition'),job,self.config)
 def test_focus_requires_complete_source_roles(self):
  with self.assertRaisesRegex(ValueError,'every compiled'):P.workload_for_job(self.profile(True),{'phase':'prerequisites','ordered_modules':['Another']},self.config)
 def test_focus_refuses_native_tactic(self):
  self.rules.write_text('Lemma bad : True. Proof. zesu_block. Qed.')
  with self.assertRaisesRegex(ValueError,'native proof'):P.workload_for_job(self.profile(True),{'phase':'prerequisites','ordered_modules':['Fixture.Rules']},self.config)
 def test_family_does_not_reduce_rule_compile(self):self.assertIsNone(P.workload_for_job(self.profile(),{'phase':'prerequisites'},self.config))
 def test_family_peak17_reports_below_twice_claim(self):self.assertTrue(L.claim_report_required(17*P.GIB,16*P.GIB,family=True));self.assertFalse(L.claim_report_required(17*P.GIB,16*P.GIB))
 def test_family_retains_peak_after_current_falls(self):self.assertTrue(L.claim_report_required(P.GIB,16*P.GIB,family=True,peak_bytes=17*P.GIB))
 def test_family_threshold_is_strict(self):self.assertFalse(L.claim_report_required(16*P.GIB,16*P.GIB,family=True))
 def test_family_report_sends_no_stop(self):
  out=self.root/'run';out.mkdir();(out/'BATCH-IDENTITY.json').write_text('{}')
  class Child:
   polls=0
   def poll(self):self.polls+=1;return None if self.polls==1 else 0
   def wait(self):return 0
  sample=dict(CPU_seconds=1,raw_cpu_stat={},memory_current_bytes=P.GIB,memory_peak_bytes=17*P.GIB,memory_events={'available':True,'counters':{}})
  with patch.object(L,'exact_aggregate',return_value=self.root),patch.object(L,'sample_aggregate',return_value=sample),patch.object(L,'search_accounting',return_value={'origin_cpu':None,'end_cpu':None}),patch.object(L.time,'sleep'),patch.object(L.subprocess,'run') as stop:
   self.assertEqual(L.wait_with_limits(Child(),out,16*P.GIB,family=True),0);stop.assert_not_called()
  self.assertTrue(json.loads((out/'MEMORY-CLAIM-REPORT.json').read_text())['report_only']);self.assertFalse((out/'EXTERNAL-STOP.json').exists())
 def guard(self,phase,claim):
  library=(HERE/'runtime-tools/resource_guard.sh').read_text().split('\nprune_scope_registry\n',1)[0];env={k:v for k,v in os.environ.items() if not k.startswith('ZESU_')};env.update(P.environment(phase,claim),ZESU_GUARD_STATE=str(self.root/'guard'),ZESU_GATE_LOCK=str(self.root/'gate'),ZESU_RUN_REGISTRY=str(self.root/'registry'))
  return subprocess.run(['bash'],input=library+'\nvalidate_probe_scope\ntest "$MEMORY_CLAIM_BYTES" = '+str(claim)+'\n',text=True,capture_output=True,env=env)
 def test_actual_focus_guard_accepts8_and24(self):
  r=self.guard('prerequisites',8*P.GIB);self.assertEqual(r.returncode,0,r.stderr)
 def test_actual_family_guard_accepts16_and64(self):
  r=self.guard('native',16*P.GIB);self.assertEqual(r.returncode,0,r.stderr)
 def test_actual_provider_preserves_focus_claim(self):
  tree=ast.parse((HERE/'code/entry_chain_provider.py').read_text());fn=next(x for x in tree.body if isinstance(x,ast.FunctionDef) and x.name=='prerequisite_environment');ns={'os':os,'relative':Path};exec(compile(ast.fix_missing_locations(ast.Module(body=[fn],type_ignores=[])),'<actual-provider>','exec'),ns)
  rt=dict(phase='prerequisites',coqc_wrapper='tools/entry_chain_coqc.sh',build_dir='default',ocamlpath='{workspace}/lib',runtime_path='runtime',runtime_sha256='sha',canonical_admission={'minimum_claim_bytes':8*P.GIB});env=ns['prerequisite_environment'](rt,self.root,self.root,inherited={});self.assertEqual(env['ZESU_MODULE_CLAIM_BYTES'],str(8*P.GIB));self.assertEqual(env['ZESU_MODULE_LIMIT_GIB'],'64')
class CompletedOpenTests(unittest.TestCase):
 def setUp(self):
  rows=json.loads((HERE/'test-fixtures/COMPLETED-STOCK-MEASUREMENTS.json').read_text())['rows'];self.row=next(r for r in rows if not r.get('format') and P.read(r['result']).get('status')=='native_open');self.target={'module':self.row['module'],'source_sha256':self.row['native_source']['sha256'],'statement_sha256':self.row['statement_sha256']}
 def altered(self,change):
  data=copy.deepcopy(P.read(self.row['result']));change(data);original=P.read
  return patch.object(P,'read',side_effect=lambda b:data if b==self.row['result'] else original(b))
 def test_normal_open_qualifies_without_proof_acceptance(self):self.assertIsNotNone(P.completed(self.row,self.target)[0])
 def test_cap_stop_refuses(self):
  with self.altered(lambda r:r.update(resource_reason='external_memory_stop')):self.assertIsNone(P.completed(self.row,self.target)[0])
 def test_oom_refuses(self):
  with self.altered(lambda r:r['CPU'].update(memory_events={'counters':{'oom_kill':1}})):self.assertIsNone(P.completed(self.row,self.target)[0])
 def test_missing_final_accounting_refuses(self):
  with self.altered(lambda r:r.update(final_memory_accounting_available=False)):self.assertIsNone(P.completed(self.row,self.target)[0])
if __name__=='__main__':unittest.main()
