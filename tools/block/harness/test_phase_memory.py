import _historical_fixtures as historical
historical.prepare()
from pathlib import Path
import ast,copy,fcntl,hashlib,json,os,subprocess,sys,tempfile,unittest
HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE/'code'))
import memory_policy as P
ROWS=[row for row in historical.read_json(HERE/'test-fixtures/COMPLETED-STOCK-MEASUREMENTS.json')['rows'] if row.get('format')!='legacy_r1_workload_rss_v1']
def binding(path):return {'path':str(path),'sha256':hashlib.sha256(path.read_bytes()).hexdigest()}
def native(row=ROWS[0]):return {'phase':'native','target':{'module':row['module'],'statement_sha256':row['statement_sha256'],'source_sha256':row['native_source']['sha256']}}
class PolicyControls(unittest.TestCase):
 def setUp(self):self.temp=tempfile.TemporaryDirectory();self.root=Path(self.temp.name)
 def tearDown(self):self.temp.cleanup()
 def changed(self,change):
  row=copy.deepcopy(ROWS[0]);value=P.read(row['result']);change(value);path=self.root/'RESULT.json';path.write_text(json.dumps(value));row['result']=binding(path);return row
 def test_seven_actual_completed_stock_bases(self):
  for row in [r for r in ROWS if r.get('format')!='completed_stock_verification_repair_v1']:
   job=P.apply_job(native(row),[row]);self.assertEqual(P.validate_job(job),8*P.GIB);self.assertEqual(job['physical_fence_bytes'],64*P.GIB);self.assertTrue(job['completed_stock_measurement']['scope'])
 def test_rounding_is_upward_in_eight_GiB_steps(self):
  self.assertEqual(P.rounded_claim(1),8*P.GIB);self.assertEqual(P.rounded_claim(16*P.GIB),24*P.GIB);self.assertEqual(P.rounded_claim(16*P.GIB+1),32*P.GIB)
 def test_unknown_native_keeps_full_fence_claim(self):self.assertEqual(P.apply_job(native())['claim_bytes'],64*P.GIB)
 def test_oom_basis_cannot_reduce_native_claim(self):
  row=self.changed(lambda value:value['CPU'].update(memory_events={'counters':{'oom_kill':1}}));self.assertEqual(P.apply_job(native(),[row])['claim_bytes'],64*P.GIB)
 def test_interrupted_basis_cannot_reduce_native_claim(self):
  row=self.changed(lambda value:value['complete_state'].update(state_source='retained_pre_call_state'));self.assertEqual(P.apply_job(native(),[row])['claim_bytes'],64*P.GIB)
 def test_partial_groups_cannot_reduce_native_claim(self):
  partial=self.root/'state.json';partial.write_text('{}');row=self.changed(lambda value:value.update(complete_state=dict(binding(partial),state_source='successful_command_returned_state')));self.assertEqual(P.apply_job(native(),[row])['claim_bytes'],64*P.GIB)
 def test_missing_final_accounting_refuses(self):
  row=self.changed(lambda value:value.update(final_memory_accounting_available=False));self.assertEqual(P.apply_job(native(),[row])['claim_bytes'],64*P.GIB)
 def test_private_route_refuses(self):
  row=dict(ROWS[0],route='private_opening');self.assertEqual(P.apply_job(native(),[row])['claim_bytes'],64*P.GIB)
 def test_unmatched_source_refuses(self):
  job=native();job['target']['source_sha256']='0'*64;self.assertEqual(P.apply_job(job,ROWS)['claim_bytes'],64*P.GIB)
 def test_compile_and_kernel_fences_are_24(self):
  for phase in ['prerequisites','compile_only','kernel']:
   job=P.apply_job({'phase':phase});self.assertEqual(P.validate_job(job),24*P.GIB);self.assertEqual(job['physical_fence_bytes'],64*P.GIB)
 def test_parent_and_native_fences_stay_fixed(self):self.assertEqual(P.PARENT_FENCE,175*P.GIB);self.assertEqual(P.NATIVE_FENCE,64*P.GIB)
 def test_reduced_native_environment_preserves_physical_fence(self):
  env=P.environment('native',8*P.GIB);self.assertEqual(env['ZESU_MODULE_CLAIM_BYTES'],str(8*P.GIB));self.assertEqual(env['ZESU_MODULE_LIMIT_GIB'],'64');self.assertEqual(env['ROCQ_MAX_PET_RSS_MB'],'65536')
 def test_native_reduced_claim_requires_bound_basis(self):
  job=P.apply_job(native());job['claim_bytes']=8*P.GIB
  with self.assertRaises(ValueError):P.validate_job(job)
 def test_active_reserve_uses_eight_not_sixtyfour(self):
  source=ast.parse((HERE/'code/check_entry_outside.py').read_text());function=next(x for x in source.body if isinstance(x,ast.FunctionDef) and x.name=='reserve')
  ledger=self.root/'ledger';ledger.write_text(json.dumps({'fixed_claims':{}}));receipt=self.root/'admission';lock=self.root/'lock'
  def save(path,value):Path(path).write_text(json.dumps(value))
  namespace={'Path':Path,'fcntl':fcntl,'time':__import__('time'),'strict_loads':json.loads,'atomic_json':save,'digest':lambda path:binding(Path(path))['sha256'],'canonical_functions':lambda policy:(lambda data,legacy:{},lambda:200*P.GIB)}
  exec(compile(ast.fix_missing_locations(ast.Module(body=[function],type_ignores=[])),'<actual-reserve>','exec'),namespace)
  job=P.apply_job(native(),ROWS);policy={'physical_fence_bytes':64*P.GIB,'minimum_claim_bytes':job['claim_bytes'],'memory_job':job,'lock':str(lock),'ledger':str(ledger),'legacy_release_bindings':{},'capture_headroom_bytes':0}
  result=namespace['reserve'](policy,'isolated-test',{'pid':os.getpid()},receipt)
  self.assertEqual(result['claim_bytes'],8*P.GIB);self.assertEqual(json.loads(ledger.read_text())['fixed_claims']['isolated-test'],8*P.GIB)
 def guard(self,phase,claim=None,script='validate_probe_scope',available=30):
  guard=HERE/'runtime-tools/resource_guard.sh';library=guard.read_text().split('\nprune_scope_registry\n',1)[0]
  env={key:value for key,value in os.environ.items() if not key.startswith('ZESU_')};env.update(P.environment(phase,claim));env.update(ZESU_GUARD_STATE=str(self.root/'guard'),ZESU_GATE_LOCK=str(self.root/'gate.lock'),ZESU_RUN_REGISTRY=str(self.root/'registry'),ZESU_RUN_REGISTRY_TOOL=str(HERE/'runtime-tools/run_registry.py'))
  return subprocess.run(['bash'],input=library+'\navailable_gib(){ echo '+str(available)+'; }\n'+script,text=True,capture_output=True,env=env)
 def test_actual_native_guard_accepts_reduced_claim(self):
  r=self.guard('native',8*P.GIB,script='validate_probe_scope && test "$MEMORY_CLAIM_BYTES" = 8589934592 && test "$MODULE_LIMIT_GIB" = 64 && memory_hold_reason');self.assertEqual(r.returncode,0,r.stderr);self.assertEqual(r.stdout,'')
 def test_actual_compile_guard_accepts_24(self):
  r=self.guard('prerequisites',script='validate_probe_scope && test "$MODULE_LIMIT_GIB" = 64');self.assertEqual(r.returncode,0,r.stderr)
 def test_actual_provider_exports_compile_phase(self):
  source=ast.parse((HERE/'code/entry_chain_provider.py').read_text());fn=next(x for x in source.body if isinstance(x,ast.FunctionDef) and x.name=='prerequisite_environment');space={'os':os,'relative':Path};exec(compile(ast.fix_missing_locations(ast.Module(body=[fn],type_ignores=[])),'<actual-provider>','exec'),space)
  runtime={'phase':'prerequisites','coqc_wrapper':'tools/entry_chain_coqc.sh','build_dir':'default','ocamlpath':'{workspace}/lib','runtime_path':'runtime','runtime_sha256':'sha'};env=space['prerequisite_environment'](runtime,self.root,self.root,inherited={});self.assertEqual(env['ZESU_MODULE_LIMIT_GIB'],'64');self.assertEqual(env['ZESU_GATE_MODULE_LIMIT_GIB'],'64');self.assertEqual(env['ROCQ_MAX_PET_RSS_MB'],'65536')
 def test_actual_shell_wrapper_preserves_native_claim_and_compile_fence(self):
  import shutil
  tools=self.root/'tools';(tools/'block').mkdir(parents=True);wrapper=tools/'entry_chain_coqc.sh';shutil.copy2(HERE/'runtime-tools/entry_chain_coqc.sh',wrapper);(tools/'block/entry_chain_compiler.py').write_text('import os,json;print(json.dumps(dict(os.environ)))')
  for phase,claim,expected in [('native',8*P.GIB,'64'),('prerequisites',24*P.GIB,'24')]:
   env=dict(os.environ,OPAM_SWITCH_PREFIX='/home/cody/islaris/_opam',**P.environment(phase,claim));r=subprocess.run(['bash',str(wrapper),'-q','source.v'],capture_output=True,text=True,env=env);self.assertEqual(r.returncode,0,r.stderr);value=json.loads(r.stdout);self.assertEqual(value['ZESU_MODULE_LIMIT_GIB'],'64');self.assertEqual(value['ZESU_MODULE_CLAIM_BYTES'],str(claim))
if __name__=='__main__':unittest.main()
