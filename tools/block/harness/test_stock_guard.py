from pathlib import Path
import ast,json,os,subprocess,tempfile,unittest,shutil
HERE=Path(__file__).parent
GUARD=HERE/'runtime-tools/resource_guard.sh'
LIBRARY=GUARD.read_text().split('\nprune_scope_registry\n',1)[0]
class StockGuardControls(unittest.TestCase):
 def run_guard(self,script,**values):
  with tempfile.TemporaryDirectory() as tmp:
   env={k:v for k,v in os.environ.items() if not k.startswith('ZESU_')}
   env.update(ZESU_GUARD_STATE=tmp,ZESU_GATE_LOCK=tmp+'/gate.lock',ZESU_RUN_REGISTRY=tmp+'/registry',ZESU_RUN_REGISTRY_TOOL=str(HERE/'runtime-tools/run_registry.py'),ZESU_DIAGNOSTIC_PROBE='1',ZESU_PROBE_ISSUE='10',ZESU_MODULE_LIMIT_GIB='64',ZESU_PROOF_CPU_LIMIT='unlimited')
   env.update(values)
   return subprocess.run(['bash'],input=LIBRARY+'\n'+script,text=True,capture_output=True,env=env)
 def validate_environment(self,environment):
  self.assertEqual(environment['ZESU_MODULE_LIMIT_GIB'],'64')
  self.assertEqual(environment['ZESU_GATE_MODULE_LIMIT_GIB'],'64')
  r=self.run_guard('validate_probe_scope',**{k:v for k,v in environment.items() if k.startswith('ZESU_')})
  self.assertEqual(r.returncode,0,r.stderr)
 def test_actual_provider_environment_passes_guard(self):
  source=ast.parse((HERE/'code/entry_chain_provider.py').read_text())
  function=next(n for n in source.body if isinstance(n,ast.FunctionDef) and n.name=='prerequisite_environment')
  namespace={'os':os,'relative':lambda value:Path(value)}
  exec(compile(ast.fix_missing_locations(ast.Module(body=[function],type_ignores=[])),'<provider-env>','exec'),namespace)
  runtime={'phase':'native','coqc_wrapper':'tools/entry_chain_coqc.sh','build_dir':'artifacts','ocamlpath':'{workspace}/lib','runtime_path':'runtime.json','runtime_sha256':'0'*64}
  environment=namespace['prerequisite_environment'](runtime,Path('/tmp/workspace'),Path('/tmp/output'),inherited={})
  self.validate_environment(environment)
 def test_actual_compiler_wrapper_environment_passes_guard(self):
  with tempfile.TemporaryDirectory() as tmp:
   tools=Path(tmp);(tools/'block').mkdir();wrapper=tools/'entry_chain_coqc.sh'
   shutil.copy2(HERE/'runtime-tools/entry_chain_coqc.sh',wrapper)
   (tools/'block/entry_chain_compiler.py').write_text('import os,json;print(json.dumps(dict(os.environ)))')
   r=subprocess.run(['bash',str(wrapper),'-q','source.v'],capture_output=True,text=True,env=dict(os.environ,OPAM_SWITCH_PREFIX='/home/cody/islaris/_opam'))
   self.assertEqual(r.returncode,0,r.stderr);self.validate_environment(json.loads(r.stdout))
 def test_actual_probe_validation_accepts_64(self):
  r=self.run_guard('validate_probe_scope');self.assertEqual(r.returncode,0,r.stderr)
 def test_actual_probe_validation_refuses_24(self):
  r=self.run_guard('validate_probe_scope',ZESU_MODULE_LIMIT_GIB='24');self.assertEqual(r.returncode,2,r.stderr)
 def test_actual_64_aggregate_properties(self):
  unit=f'zesuworkloads-aggregate{os.getuid()}p{os.getpid()}r64001.slice'
  command=['/usr/bin/systemctl','--user']
  try:
   r=subprocess.run(command+['set-property','--runtime',unit,'MemoryMax=64G','MemorySwapMax=0'],capture_output=True,text=True)
   self.assertEqual(r.returncode,0,r.stderr)
   r=self.run_guard('validate_probe_scope && aggregate_slice',ZESU_AGGREGATE_SLICE=unit,ZESU_AGGREGATE_LIMIT='64G')
   self.assertEqual(r.returncode,0,r.stderr);self.assertEqual(r.stdout.strip(),unit)
   r=self.run_guard('aggregate_slice',ZESU_AGGREGATE_SLICE=unit,ZESU_AGGREGATE_LIMIT='24G')
   self.assertEqual(r.returncode,2,r.stderr)
  finally:
   r=subprocess.run(command+['stop',unit],capture_output=True,text=True);self.assertEqual(r.returncode,0,r.stderr)
   r=subprocess.run(command+['revert',unit],capture_output=True,text=True);self.assertEqual(r.returncode,0,r.stderr)
if __name__=='__main__':unittest.main()
