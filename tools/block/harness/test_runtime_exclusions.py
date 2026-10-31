import json
"""Run both collector phases without MCP, PET, or a proof."""
from copy import deepcopy
import concurrent.futures,importlib.util,os,subprocess,sys,tempfile,unittest
from pathlib import Path
HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE/'code'))
import proof_cache_key as key
import collector
import result_cache
from runtime_ignores import excluded,python_argv
loader=importlib.util.spec_from_file_location('cache_fixture','/home/cody/zesislar/tools/test_proof_cache_key.py')
fixture_module=importlib.util.module_from_spec(loader);loader.loader.exec_module(fixture_module);fixture_module.keys=key
sys.path.insert(0,str(HERE/'code'))
class TwoPhase(unittest.TestCase):
 def setUp(self):
  f=fixture_module.ProofCacheKeyTests(methodName='runTest');f.setUp();self.addCleanup(f.doCleanups);self.work=f.work;self.spec=f.spec
  self.private=self.work/'private';self.private.mkdir();self.runtime=self.work/'runtime';self.runtime.mkdir()
  c=self.spec['recipe']['configuration'];c['locale']='C'
  c['environment'].update({n:{'kind':'literal','value':v} for n,v in {'LANG':'C','LC_ALL':'C','LC_CTYPE':'C','PYTHONHASHSEED':'0','PYTHONNOUSERSITE':'1','PYTHONDONTWRITEBYTECODE':'1','PYTHONCOERCECLOCALE':'0','PYTHONUTF8':'1'}.items()})
  self.policy={'schema':collector.SCHEMA,'python':collector.binding(self.work/'coqc'),'probe':collector.binding(self.work/'provider.py'),'python_entry':collector.binding(self.work/'provider.py'),'python_modules':[],'python_search_prefix':[],'ldd':collector.binding(self.work/'coqc'),'trees':[{'path':str(self.work),'role':'python_dependencies'}],'cache_directories':[str(self.private)],'executables':[],'module_resolution':[]}
  self.transients=[self.runtime/p for p in ['__pycache__/entry_chain_run.cpython-312.pyc','other.pyc','.lia.cache','.nia.cache','_build/log','_build/custom/trace.csexp']]
  for path in self.transients:
   path.parent.mkdir(parents=True,exist_ok=True);path.write_text('old cache');name='runtime:runtime_code:'+str(path.relative_to(self.runtime))
   self.spec['files'].append(dict(collector.binding(path),id=name,kind='runtime_file',root_role='workspace'));self.spec['recipe']['dependencies'].append({'id':name,'requires':[]})
  self.source=self.runtime/'generated/isla-traces/semantics.v';self.source.parent.mkdir(parents=True);self.source.write_text('source');self.obj=self.source.with_suffix('.vo');self.obj.write_text('object')
 def probe(self,p,e,cwd):
  return {'executable':str(self.work/'coqc'),'environment':e,'version_short':'3.12.11','locale':{'LC_CTYPE':'C'},'hash_randomization':False,'modules':[],'distributions':[],'sysconfig':{n:str(self.work) for n in ['stdlib','platstdlib','purelib','platlib']},'sys_path':[str(self.work)]}
 def collect(self,spec=None):return collector.collect(self.spec if spec is None else spec,self.policy,probe=self.probe)
 def test_two_phase_mutable_caches(self):
  first=self.collect();before=key.build_keys(first['input'])
  for p in self.transients:p.write_text('different bytes')
  self.assertTrue(collector.revalidate(first,probe=self.probe));second=self.collect(first['input'])
  self.assertEqual(before,key.build_keys(second['input']));self.assertFalse(any(excluded(r['path']) for r in second['input']['files']))
 def test_two_phase_concurrent_imports(self):
  module=self.runtime/'race_import.py';module.write_text('VALUE=17\n');first=self.collect()
  argv=[sys.executable,'-B','-c',"import importlib.util,py_compile,sys;p=sys.argv[1];py_compile.compile(p,cfile=p+'c');s=importlib.util.spec_from_file_location('race_import',p);m=importlib.util.module_from_spec(s);s.loader.exec_module(m);assert m.VALUE==17",str(module)]
  with concurrent.futures.ThreadPoolExecutor(max_workers=4) as pool:
   for r in pool.map(lambda _:subprocess.run(argv,env=dict(os.environ,PYTHONDONTWRITEBYTECODE='1'),capture_output=True,text=True),range(8)):self.assertEqual(r.returncode,0,r.stderr)
  self.assertEqual(key.build_keys(first['input']),key.build_keys(self.collect(first['input'])['input']))
 def test_source_change_refuses(self):
  first=self.collect();self.source.write_text('changed')
  with self.assertRaisesRegex(ValueError,'bound dependency changed'):self.collect(first['input'])
 def test_object_change_refuses(self):
  first=self.collect();self.obj.write_text('changed')
  with self.assertRaisesRegex(ValueError,'bound dependency changed'):self.collect(first['input'])
 def test_semantics_and_pinned_binary_remain_bound(self):
  files={r['path'] for r in self.collect()['input']['files']};self.assertTrue({str(self.source),str(self.obj),str(self.work/'coqc')}<=files)
 def test_new_source_refuses(self):
  first=self.collect();(self.runtime/'new.v').write_text('new')
  with self.assertRaisesRegex(ValueError,'directory changed'):collector.revalidate(first,probe=self.probe)
class OutputNames(unittest.TestCase):
 def test_names(self):
  for p in ['a/__pycache__/x','a/x.pyc','a/.lia.cache','a/.nia.cache','a/_build/log','a/_build/sub/trace.csexp']:self.assertTrue(excluded(p),p)
  for p in ['generated/isla-traces/x.v','generated/isla-traces/x.vo','binary','trace.json','trace.v','a/log','a/trace.csexp','_build/trace.v','declaration-input.json']:self.assertFalse(excluded(p),p)
 def test_python_flags(self):
  a=['/venv/bin/python','relay.py','--','/venv/bin/python','server.py'];b=['/venv/bin/python','-B','relay.py','--','/venv/bin/python','-B','server.py'];self.assertEqual(python_argv(a),b);self.assertEqual(python_argv(b),b)
if __name__=='__main__':unittest.main()

class ToolTransition(unittest.TestCase):
 def fixture(self):
  import scratch,clone_copy,restart_bindings
  temporary=tempfile.TemporaryDirectory(dir=HERE.parent);self.addCleanup(temporary.cleanup);workspace=Path(temporary.name)
  from unittest.mock import patch
  gate=patch('harness_commit.check');gate.start();self.addCleanup(gate.stop)
  layout=json.loads((HERE/'TOOL-LAYOUT.json').read_text())
  manifest={'files':[scratch.binding(HERE/source) for source in layout.values()],'relative_paths':{str((HERE/source).resolve()):relative for relative,source in layout.items()}}
  c={'harness':{'commit':'fixture'},'prepared_workspace':str(workspace),'adoption_implementation':scratch.binding(HERE/'code/full_chain.py'),'guard_override':scratch.binding(HERE/'runtime-tools/resource_guard.sh'),'guard_override_base':scratch.binding(HERE/'runtime-tools/resource_guard.sh'),'job_controller':scratch.binding(HERE/'code/entry_chain_run.py'),'admission':{'reviewed_helpers':str(HERE/'code/entry_admission')},'aggregate_memory_ceiling_bytes':64*1024**3,'cache_attempt':{'limits':{'memory_bytes':64*1024**3}},'jobs':[]}
  transitions=[]
  for row in manifest['files']:
   rel=manifest['relative_paths'][row['path']];dest=workspace/'tools'/rel;dest.parent.mkdir(parents=True,exist_ok=True);clone_copy.copy2(row['path'],dest)
   if rel=='entry_chain_coqc.sh':dest.write_text('exact old prepared tool')
   transitions.append({'relative':rel,'prepared':scratch.binding(dest),'successor':row})
  c['prepared_tool_transition']=transitions
  return c,workspace
 def test_exact_old_tools_then_successor_install(self):
  import clone_copy,restart_bindings,scratch
  c,workspace=self.fixture();self.assertTrue(restart_bindings.verify_restart_runtime(c,HERE));copy=workspace.parent/(workspace.name+'-owned');self.addCleanup(lambda:__import__('shutil').rmtree(copy,ignore_errors=True));clone_copy.copytree(workspace,copy)
  report=restart_bindings.install_restart_tools(copy,deepcopy(c),HERE)
  for row in report['copies']:
   self.assertEqual(scratch.binding(row['owned']['path'])['sha256'],row['source']['sha256']);self.assertTrue(row['distinct_inode'])
  self.assertEqual((workspace/'tools/entry_chain_coqc.sh').read_text(),'exact old prepared tool')
 def test_wrong_old_tool_refuses(self):
  import restart_bindings
  c,workspace=self.fixture();(workspace/'tools/entry_chain_coqc.sh').write_text('changed after transition binding')
  with self.assertRaisesRegex(ValueError,'stale or changed'):restart_bindings.verify_restart_runtime(c,HERE)
 def test_missing_new_dependency_refuses_old_bank(self):
  import restart_bindings
  c,workspace=self.fixture();missing=workspace/'tools/block/binding_cache.py';missing.unlink()
  with self.assertRaises(FileNotFoundError):restart_bindings.verify_restart_runtime(c,HERE)
  self.assertFalse(missing.exists())
 def test_fresh_owned_clone_installs_missing_dependency(self):
  import clone_copy,restart_bindings,scratch
  c,workspace=self.fixture();missing=workspace/'tools/block/binding_cache.py';missing.unlink()
  copy=workspace.parent/(workspace.name+'-fresh');self.addCleanup(lambda:__import__('shutil').rmtree(copy,ignore_errors=True));clone_copy.copytree(workspace,copy)
  report=restart_bindings.install_restart_tools(copy,deepcopy(c),HERE)
  row=next(row for row in report['copies'] if row['owned']['path']==str(copy/'tools/block/binding_cache.py'))
  self.assertIsNone(row['previous']);self.assertTrue(row['distinct_inode'])
  self.assertEqual(scratch.binding(copy/'tools/block/binding_cache.py')['sha256'],scratch.binding(HERE/'code/binding_cache.py')['sha256'])
  self.assertFalse(missing.exists())
 def test_unlisted_old_tool_refuses(self):
  import restart_bindings
  c,workspace=self.fixture();c['prepared_tool_transition']=c['prepared_tool_transition'][:-1]
  with self.assertRaisesRegex(ValueError,'exact successor'):restart_bindings.verify_restart_runtime(c,HERE)
 def test_B_keeps_actor_classification(self):
  import entry_chain_resources as resources
  for name in ['complete_goals_mcp.py','entry_chain_provider.py','entry_chain_run.py']:
   argv=['/venv/bin/python','-B',str(resources.P/name)]+(['--inside','out'] if name=='entry_chain_run.py' else [])
   self.assertTrue(resources.proof_actor({'exe':'/venv/bin/python','argv':argv}))
