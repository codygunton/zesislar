import ast,copy,hashlib,json,os,subprocess,sys,tempfile,unittest
from pathlib import Path
from unittest.mock import patch
HERE=Path(__file__).resolve().parent
sys.path[:0]=[str(HERE/'code'),str(HERE.parents[0]),str(HERE.parents[1])]
import _historical_fixtures as historical
historical.prepare()
import memory_policy as P
import scratch_limits as L

def binding(p):return {'path':str(p),'sha256':hashlib.sha256(Path(p).read_bytes()).hexdigest()}
class Controls(unittest.TestCase):
 def setUp(self):
  self.temp=tempfile.TemporaryDirectory(dir=str(HERE.parent));self.addCleanup(self.temp.cleanup);self.root=Path(self.temp.name)
  self.profile=json.loads((historical.materialize('/home/cody/zesislar/_build/agents/worker-build-2/private-admission-route-v1/PROFILE-measured-6ae0.json')).read_text())
  self.original=P.read
  prior=P.read(self.profile['observed_growth']['runtime'])
  self.raw_job={'phase':'native','target':prior['target']['block'],'native_route':self.profile['authority'],'ordered_modules':[]}
 def job(self,profile=None):
  profile=profile or self.profile;p=self.root/'profile.json';p.write_text(json.dumps(profile))
  workload={'kind':'minimal_native_tactic','profile':binding(p),'owned_sources':[],'declarations_only':False,'native_route':profile['authority']}
  # Only source authority dispatch is replaced. Real bound memory evidence and all policy checks run.
  with patch.object(P,'workload_for_job',return_value=workload):return P.apply_job(self.raw_job,workload=workload)
 def validated(self,j):
  with patch.object(P,'workload_for_job',return_value=j['workload']):return P.validate_job(j)
 def environment(self,j):
  with patch.object(P,'workload_for_job',return_value=j['workload']):return P.environment(j['phase'],j['claim_bytes'],job=j)
 def test_current_completed_6ae0_peak_derives16_fence_and8_claim(self):
  j=self.job();self.assertEqual(self.validated(j),8*P.GIB);self.assertEqual(j['physical_fence_bytes'],16*P.GIB)
 def test_completed69b0_peak_derives8_fence(self):
  self.profile=json.loads((historical.materialize('/home/cody/zesislar/_build/agents/worker-build-2/private-admission-route-v1/PROFILE-measured-69b0.json')).read_text());prior=P.read(self.profile['observed_growth']['runtime']);self.raw_job['target']=prior['target']['block'];self.raw_job['native_route']=self.profile['authority']
  self.assertEqual(self.job()['physical_fence_bytes'],8*P.GIB)
 def test_measured_environment_removes_inherited_issue10(self):
  env=dict(ZESU_DIAGNOSTIC_PROBE='1',ZESU_PROBE_ISSUE='10');env.update(self.environment(self.job()));self.assertEqual(env['ZESU_DIAGNOSTIC_PROBE'],'0');self.assertEqual(env['ZESU_PROBE_ISSUE'],'');self.assertEqual(env['ZESU_AGGREGATE_LIMIT'],'16G')
 def test_true_diagnostic_every_phase_has64_fence(self):
  for phase in ['native','prerequisites','compile_only','kernel']:
   env=P.environment(phase,8*P.GIB);self.assertEqual(env['ZESU_MODULE_LIMIT_GIB'],'64');self.assertEqual(env['ZESU_DIAGNOSTIC_PROBE'],'1');self.assertEqual(env['ZESU_PROBE_ISSUE'],'10')
 def test_declaration_claim_stays24_with64_fence(self):
  j=P.apply_job({'phase':'prerequisites'});self.assertEqual(P.validate_job(j),24*P.GIB);self.assertEqual(j['physical_fence_bytes'],64*P.GIB)
 def test_focused_diagnostic_claim8_fence64(self):
  profile=self.root/'focus.json';profile.write_text(json.dumps({'schema':'scratch.admission-profile.v1','kind':'focused_check','sources':[],'memory_route':'diagnostic'}));j={'phase':'prerequisites','ordered_modules':[]};w=P.workload_for_job(binding(profile),j,{'proof_runtime':{'module_files':{}},'prepared_workspace':str(self.root),'declarations_only':True});j=P.apply_job(j,workload=w);self.assertEqual(P.validate_job(j),8*P.GIB);self.assertEqual(j['physical_fence_bytes'],64*P.GIB)
 def test_missing_measurement_refuses(self):
  del self.profile['observed_growth']
  with self.assertRaisesRegex(ValueError,'completed accounting'):self.job()
 def test_missing_completion_refuses(self):
  del self.profile['observed_completion']['release']
  with self.assertRaisesRegex(ValueError,'lifecycle'):self.job()
 def test_accounting_tamper_refuses(self):
  self.profile['observed_growth']['accounting']['sha256']='0'*64
  with self.assertRaisesRegex(ValueError,'binding changed'):self.job()
 def test_wrong_source_refuses(self):
  self.raw_job['target']=dict(self.raw_job['target'],source_sha256='0'*64)
  with self.assertRaisesRegex(ValueError,'another block'):self.job()
 def test_changed_fence_refuses(self):
  j=self.job();j['physical_fence_bytes']=8*P.GIB
  with self.assertRaises(ValueError):self.validated(j)
 def test_changed_claim_refuses(self):
  j=self.job();j['claim_bytes']=P.GIB
  with self.assertRaises(ValueError):self.validated(j)
 def test_wrong_environment_phase_refuses(self):
  j=self.job()
  with self.assertRaisesRegex(ValueError,'phase differs'):P.environment('prerequisites',job=j)
 def altered(self,key,change):
  wanted=self.profile['observed_completion'].get(key) or self.profile['observed_growth'][key];value=copy.deepcopy(P.read(wanted));change(value)
  return patch.object(P,'read',side_effect=lambda row:value if row==wanted else self.original(row))
 def test_open_actor_refuses(self):
  with self.altered('closure',lambda x:x.update(all_owned_actors_closed=False)):
   with self.assertRaisesRegex(ValueError,'closure'):self.job()
 def test_unreleased_claim_refuses(self):
  with self.altered('release',lambda x:x.update(released=False)):
   with self.assertRaisesRegex(ValueError,'release'):self.job()
 def test_pre_call_result_refuses(self):
  with self.altered('result',lambda x:x.update(normal_tactic_return=False)):
   with self.assertRaisesRegex(ValueError,'return is incomplete'):self.job()
 def test_foreign_lifecycle_path_refuses(self):
  p=self.root/'RELEASE.json';p.write_text(Path(self.profile['observed_completion']['release']['path']).read_text());self.profile['observed_completion']['release']=binding(p)
  with self.assertRaisesRegex(ValueError,'exact job'):self.job()
 def test_live_growth_accounting_refuses(self):
  self.profile['observed_growth']['accounting']=self.profile['observed_completion']['result']
  with self.assertRaises(ValueError):self.job()
 def guard(self,env,body):
  lib=(HERE/'runtime-tools/resource_guard.sh').read_text().split('\nprune_scope_registry\n',1)[0]
  env=dict({k:v for k,v in os.environ.items() if not k.startswith('ZESU_')},**env,ZESU_GUARD_STATE=str(self.root/'state'),ZESU_GATE_LOCK=str(self.root/'lock'),ZESU_RUN_REGISTRY=str(self.root/'registry'))
  return subprocess.run(['bash'],input=lib+'\n'+body,text=True,capture_output=True,env=env)
 def test_actual_guard_measured_acceptance_and_marker_omission(self):
  r=self.guard(self.environment(self.job()),'validate_probe_scope || exit $?\nif diagnostic_probe; then echo probe=issue10; else echo ordinary; fi\ntest "$MODULE_LIMIT_GIB" = 16\n');self.assertEqual(r.returncode,0,r.stderr);self.assertEqual(r.stdout,'ordinary\n')
 def test_actual_guard_true_diagnostic64_accepts(self):
  r=self.guard(P.environment('prerequisites',8*P.GIB),'validate_probe_scope && diagnostic_probe && test "$MODULE_LIMIT_GIB" = 64');self.assertEqual(r.returncode,0,r.stderr)
 def test_actual_guard_issue10_24_refuses(self):
  env=P.environment('prerequisites',8*P.GIB);env.update(ZESU_MODULE_LIMIT_GIB='24',ZESU_GATE_MODULE_LIMIT_GIB='24')
  self.assertNotEqual(self.guard(env,'validate_probe_scope').returncode,0)
 def test_actual_compiler_wrapper_preserves_both_routes(self):
  tools=self.root/'tools';(tools/'block').mkdir(parents=True);wrapper=tools/'entry_chain_coqc.sh';wrapper.write_bytes((HERE/'runtime-tools/entry_chain_coqc.sh').read_bytes());(tools/'block/entry_chain_compiler.py').write_text('import os,json;print(json.dumps(dict(os.environ)))')
  for env in [self.environment(self.job()),P.environment('prerequisites',8*P.GIB)]:
   r=subprocess.run(['bash',str(wrapper),'source.v'],capture_output=True,text=True,env=dict(os.environ,OPAM_SWITCH_PREFIX='/home/cody/islaris/_opam',**env));self.assertEqual(r.returncode,0,r.stderr);actual=json.loads(r.stdout)
   for key in ['ZESU_MODULE_LIMIT_GIB','ZESU_MODULE_CLAIM_BYTES','ZESU_DIAGNOSTIC_PROBE','ZESU_PROBE_ISSUE']:self.assertEqual(actual[key],env[key])
 def test_cpu_stops_unchanged(self):
  self.assertEqual(L.CPU_STOP_SECONDS,7200);self.assertIsNone(L.SETUP_CPU_STOP_SECONDS);self.assertIsNone(L.stop_reason(7200,0,8*P.GIB));self.assertEqual(L.stop_reason(7201,0,8*P.GIB,origin_cpu=1),'external_CPU_stop');self.assertEqual(P.PARENT_FENCE,175*P.GIB)
 def test_measured_memory_stop_uses_actual_fence(self):
  j=self.job()
  with patch.object(P,'workload_for_job',return_value=j['workload']):
   self.assertEqual(L.stop_reason(1,16*P.GIB,8*P.GIB,memory_job=j),'external_memory_stop');self.assertIsNone(L.stop_reason(1,15*P.GIB,8*P.GIB,memory_job=j))
 def test_no_numeric_only_measured_actor_permission(self):
  from entry_chain_resources import validate_limits
  with self.assertRaisesRegex(Exception,'bound memory job'):validate_limits({},16*P.GIB)
 def test_admission_policy_matches_real_job(self):
  j=self.job();policy={'memory_job':j,'minimum_claim_bytes':j['claim_bytes'],'physical_fence_bytes':j['physical_fence_bytes']}
  with patch.object(P,'workload_for_job',return_value=j['workload']):self.assertEqual(P.admission_claim(policy),8*P.GIB);policy['physical_fence_bytes']=64*P.GIB
  with patch.object(P,'workload_for_job',return_value=j['workload']):
   with self.assertRaisesRegex(ValueError,'differs'):P.admission_claim(policy)
 def test_typed_environment_uses_same_policy_before_phase1(self):
  tree=ast.parse((HERE/'code/stage1_runtime.py').read_text());fn=next(n for n in tree.body if isinstance(n,ast.FunctionDef) and n.name=='build_collection');assign=next(n for n in fn.body if isinstance(n,ast.Assign) and any(isinstance(x,ast.Name) and x.id=='env' for x in n.targets));j=self.job()
  with patch.object(P,'workload_for_job',return_value=j['workload']):
   ns={'literal':lambda x:x,'job':j};exec(compile(ast.fix_missing_locations(ast.Module(body=[assign],type_ignores=[])),'<actual-typed-env>','exec'),ns)
  self.assertEqual(ns['env']['ZESU_DIAGNOSTIC_PROBE'],'0');self.assertEqual(ns['env']['ZESU_AGGREGATE_LIMIT'],'16G');self.assertEqual(ns['env']['ROCQ_MAX_PET_RSS_MB'],'16384')
 def test_actual_provider_preserves_diagnostic_and_measured_policy(self):
  tree=ast.parse((HERE/'code/entry_chain_provider.py').read_text());fn=next(x for x in tree.body if isinstance(x,ast.FunctionDef) and x.name=='prerequisite_environment');ns={'os':os,'relative':Path};exec(compile(ast.fix_missing_locations(ast.Module(body=[fn],type_ignores=[])),'<actual-provider>','exec'),ns)
  for job in [self.job(),P.apply_job({'phase':'prerequisites'})]:
   runtime={'phase':job['phase'],'coqc_wrapper':'tools/entry_chain_coqc.sh','build_dir':'default','ocamlpath':'{workspace}/lib','runtime_path':'runtime','runtime_sha256':'sha','canonical_admission':{'memory_job':job,'minimum_claim_bytes':job['claim_bytes']}}
   with patch.object(P,'workload_for_job',return_value=job['workload']):
    env=ns['prerequisite_environment'](runtime,self.root,self.root,inherited={'ZESU_DIAGNOSTIC_PROBE':'1','ZESU_PROBE_ISSUE':'10'})
   self.assertEqual(env['ZESU_MODULE_LIMIT_GIB'],str(job['physical_fence_bytes']//P.GIB));self.assertEqual(env['ZESU_DIAGNOSTIC_PROBE'],'0' if job['phase']=='native' else '1')
 def test_actual_aggregate_checks_real_measured_fence_and_parent(self):
  j=self.job();parent=self.root/'zesuworkloads.slice';parent.mkdir();(parent/'memory.max').write_text(str(P.PARENT_FENCE));(parent/'memory.swap.max').write_text('0');group=parent/'zesuworkloads-aggregate1000p1r1.slice';group.mkdir();(group/'memory.max').write_text(str(j['physical_fence_bytes']));(group/'memory.swap.max').write_text('0');st=group.stat();identity={'aggregate_path':str(group),'aggregate_device':st.st_dev,'aggregate_inode':st.st_ino}
  with patch.object(P,'workload_for_job',return_value=j['workload']):
   self.assertEqual(L.exact_aggregate(identity,j['physical_fence_bytes'],memory_job=j),group)
   with self.assertRaisesRegex(ValueError,'bound memory job'):L.exact_aggregate(identity,64*P.GIB,memory_job=j)
   (parent/'memory.max').write_text(str(110*P.GIB))
   with self.assertRaisesRegex(ValueError,'shared workload parent'):L.exact_aggregate(identity,j['physical_fence_bytes'],memory_job=j)
 def test_actual_guard_refuses_stale24_marker(self):
  marker=self.root/'marker';marker.write_text('probe=issue10\nmemory_gib=24\ncpu=unlimited\nowner_start=1\n')
  result=self.guard(P.environment('prerequisites',8*P.GIB),'probe_record '+str(marker)+'\n');self.assertNotEqual(result.returncode,0)
 def test_explicit_override_source_binding_precedes_compaction(self):
  source=(HERE/'scratch.py').read_text();self.assertIn("[binding(workspace/modules[row['module']]) for row in overrides]",source);self.assertLess(source.index("[binding(workspace/modules[row['module']]) for row in overrides]"),source.index("compact(c,c['seed_binding_reference']['descriptor'],c['prepared_workspace'])"))
 def test_attempt_metadata_binds_real_measured_fence(self):
  j=self.job();original={'limits':{'memory_bytes':64*P.GIB,'cpu_seconds':7200,'wall_seconds':None,'swap_bytes':0,'steps':None},'scope_limits':[{'role':role,'memory_bytes':64*P.GIB,'cpu_seconds':None,'swap_bytes':0} for role in ['workloads','aggregate','batch','client','mcp','pet','compiler']],'tool_timeouts':{'mcp':604800}}
  before=copy.deepcopy(original)
  with patch.object(P,'workload_for_job',return_value=j['workload']):value=P.attempt_for_job(original,j)
  self.assertEqual(original,before);self.assertEqual(value['limits']['memory_bytes'],16*P.GIB)
  for row in value['scope_limits']:self.assertEqual(row['memory_bytes'],(175 if row['role']=='workloads' else 16)*P.GIB)
  value['limits']['memory_bytes']=before['limits']['memory_bytes']
  for a,b in zip(value['scope_limits'],before['scope_limits']):a['memory_bytes']=b['memory_bytes']
  self.assertEqual(value,before)
 def test_attempt_diagnostic_metadata_stays64(self):
  j=P.apply_job({'phase':'prerequisites'});value=P.attempt_for_job({'limits':{'memory_bytes':24*P.GIB},'scope_limits':[{'role':'aggregate','memory_bytes':24*P.GIB}]},j);self.assertEqual(value['limits']['memory_bytes'],64*P.GIB);self.assertEqual(value['scope_limits'][0]['memory_bytes'],64*P.GIB)
 def test_staged_runtime_exercises_strict_actor_check(self):
  from entry_chain_resources import validate_limits
  tree=ast.parse((HERE/'scratch.py').read_text());fn=next(n for n in tree.body if isinstance(n,ast.FunctionDef) and n.name=='prestage_sealed');call=next(n for n in ast.walk(fn) if isinstance(n,ast.Call) and isinstance(n.func,ast.Attribute) and n.func.attr=='stage_job');job=self.job();staged=eval(compile(ast.Expression(call.args[1]),'<actual-staged-job>','eval'),{'job':job});runtime={'canonical_admission':staged['policy']}
  row={'exe':'/home/cody/islaris/_opam/bin/pet','argv':['pet'],'limits':'Max cpu time              unlimited            unlimited            seconds','effective_limits':{'memory.max':job['physical_fence_bytes'],'memory.swap.max':0}}
  with patch.object(P,'workload_for_job',return_value=job['workload']):validate_limits(row,runtime['canonical_admission']['physical_fence_bytes'],memory_job=runtime['canonical_admission']['memory_job'])
  self.assertEqual(runtime['canonical_admission']['minimum_claim_bytes'],8*P.GIB);self.assertEqual(runtime['canonical_admission']['physical_fence_bytes'],16*P.GIB)
  row['effective_limits']['memory.max']=64*P.GIB
  with patch.object(P,'workload_for_job',return_value=job['workload']):
   with self.assertRaisesRegex(Exception,'Physical proof fence differs'):validate_limits(row,runtime['canonical_admission']['physical_fence_bytes'],memory_job=runtime['canonical_admission']['memory_job'])
 def aggregate_guard(self,limit,actual=None,swap='0'):
  text=(HERE/'runtime-tools/resource_guard.sh').read_text();start=text.index('aggregate_slice() {');end=text.index('\n}',start)+2;fn=text[start:end]
  actual=str(int(limit.removesuffix('G'))*P.GIB) if actual is None else str(actual)
  script='GIB=1073741824\nsystemctl(){ printf "MemoryMax=%s\\nMemorySwapMax=%s\\n" "'+actual+'" "'+swap+'"; }\n'+fn+'\naggregate_slice\n'
  return subprocess.run(['bash'],input=script,text=True,capture_output=True,env=dict(os.environ,ZESU_IN_BATCH='1',ZESU_AGGREGATE_SLICE='zesuworkloads-aggregate1000p1r1.slice',ZESU_AGGREGATE_LIMIT=limit))
 def test_actual_aggregate_guard_accepts_reviewed_measured_quanta(self):
  for value in ['8G','16G','24G','32G']:
   result=self.aggregate_guard(value);self.assertEqual(result.returncode,0,result.stderr)
 def test_actual_aggregate_guard_keeps_legacy_limits(self):
  for value in ['64G','120G','150G']:self.assertEqual(self.aggregate_guard(value).returncode,0)
 def test_actual_aggregate_guard_refuses_unknown_limits(self):
  for value in ['0G','9G','33G','63G']:self.assertNotEqual(self.aggregate_guard(value).returncode,0)
 def test_actual_aggregate_guard_checks_physical_memory(self):self.assertNotEqual(self.aggregate_guard('8G',actual=64*P.GIB).returncode,0)
 def test_actual_aggregate_guard_checks_physical_swap(self):self.assertNotEqual(self.aggregate_guard('8G',swap='max').returncode,0)
if __name__=='__main__':unittest.main()
