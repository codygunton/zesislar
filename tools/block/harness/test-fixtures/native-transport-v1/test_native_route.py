import asyncio
from contextlib import asynccontextmanager
import copy
import hashlib
import json
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch

HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE/'code'))
import scratch
import native_route as N
import memory_policy as M
import scratch_statement as S
import launch_adapter as A
import heldout_reporting as H
from entry_chain import binding

class NativeRoute(unittest.TestCase):
 def setUp(self):
  self.temp=tempfile.TemporaryDirectory();self.addCleanup(self.temp.cleanup)
  self.root=Path(self.temp.name)
 def file(self,name,text):
  p=self.root/name;p.parent.mkdir(parents=True,exist_ok=True);p.write_text(text);return binding(p)
 def js(self,name,data):return self.file(name,json.dumps(data))
 def fixture(self,body='zesu_block.'):
  statement='Lemma DesignedBoundary_Test : True.\n'
  original=self.file('Original.v','Require Import Fixture.Base.\n'+statement+'Proof.\nzesu_block.\nQed.\n')
  native=self.file('Native.v','Require Import Fixture.Tactic.\n'+statement+'Proof.\n'+body+'\nQed.\n')
  tactic=self.file('Tactic.v','Ltac zesu_block2 := idtac.\nLtac zesu_block := zesu_block2.\n')
  rows=[dict(native,module='Fixture.Native'),dict(tactic,module='Fixture.Tactic')]
  value={'schema':'scratch.minimal-native-authority.v1','native_body':body,'ordered_modules':['Fixture.Tactic'],
         'native_source':rows[0],'original_source':original,'tactic_source':rows[1],'source_inventory':rows,
         'target_import_closure':['Fixture.Native','Fixture.Tactic']}
  obj=self.file('Tactic.vo','compiled tactic')
  receipt=self.js('compile.json',{'source':tactic['path'],'source_sha256':tactic['sha256'],'object':obj['path'],'object_sha256':obj['sha256'],'result':{'success':True}})
  common={'status':'passed','ready_runtime':self.js('ready.json',{}),'modules':[{'module':'Fixture.Tactic','source':tactic,'object':obj,'receipt':receipt}],
          'closure':self.js('closure.json',{'all_owned_actors_closed':True,'actors':[{'ended':True}],'claim_key':'common'}),
          'release':self.js('release.json',{'released':True,'claim_key':'common','bytes':24*1024**3}),
          'claim_bytes':24*1024**3,'fence_bytes':24*1024**3,'native_calls':0}
  value['common_prefix']=self.js('common.json',common);value['prerequisite_delta']=[]
  route=self.js('authority.json',value)
  target={'module':'Fixture.Native','source_sha256':native['sha256'],'statement_sha256':hashlib.sha256(statement.encode()).hexdigest()}
  config={'prepared_workspace':str(self.root),'proof_runtime':{'module_files':{'Fixture.Native':'Native.v','Fixture.Tactic':'Tactic.v'}},'declarations_only':False}
  job={'phase':'native','target':target,'ordered_modules':[],'native_route':route}
  return value,route,config,job
 def test_minimal_existing_import_preserves_exact_caller(self):
  from scratch_imports import install_rules_import
  v,r,c,j=self.fixture();p=Path(v['native_source']['path']);before=p.read_bytes()
  result=install_rules_import(p,'Fixture.Tactic',S.source_statement,r)
  self.assertTrue(result['source_unchanged']);self.assertEqual(p.read_bytes(),before)
 def test_minimal_missing_or_repeated_import_refuses(self):
  from scratch_imports import install_rules_import
  for text in ['Require Import Other.Tactic.\n','Require Import Fixture.Tactic.\nRequire Import Fixture.Tactic.\n']:
   v,r,c,j=self.fixture();p=Path(v['native_source']['path']);p.write_text(text+'Lemma DesignedBoundary_Test : True.\nProof.\nzesu_block.\nQed.\n')
   with self.assertRaisesRegex(ValueError,'exactly one|repeats'):install_rules_import(p,'Fixture.Tactic',S.source_statement,r)
 def test_stock_helper_still_requires_all(self):
  from scratch_imports import install_rules_import
  v,r,c,j=self.fixture()
  with self.assertRaisesRegex(ValueError,'Automation.All'):install_rules_import(v['native_source']['path'],'Fixture.Tactic',S.source_statement)
 def test_reviewed_source_claim8_fence64(self):
  value,route,c,j=self.fixture();profile=self.js('profile.json',{'schema':'scratch.admission-profile.v1','kind':N.KIND,'authority':route})
  work=M.workload_for_job(profile,j,c);job=M.apply_job(j,workload=work)
  self.assertEqual(M.validate_job(job),8*M.GIB);self.assertEqual(job['physical_fence_bytes'],64*M.GIB)
  self.assertEqual(M.PARENT_FENCE,175*M.GIB)
 def test_changed_native_source_refuses(self):
  v,r,c,j=self.fixture();Path(v['native_source']['path']).write_text('changed')
  with self.assertRaises(ValueError):N.validate(r,workspace=self.root,modules=c['proof_runtime']['module_files'],target=j['target'],ordered=[])
 def test_changed_tactic_source_refuses(self):
  v,r,c,j=self.fixture();Path(v['tactic_source']['path']).write_text('changed')
  with self.assertRaises(ValueError):N.authority(r)
 def test_native_phase_rejects_repeated_dependencies(self):
  v,r,c,j=self.fixture()
  with self.assertRaisesRegex(ValueError,'repeat prerequisite'):
   N.validate(r,workspace=self.root,modules=c['proof_runtime']['module_files'],target=j['target'],ordered=v['ordered_modules'])
 def test_reviewed_prerequisite_order_is_separate(self):
  v,r,c,j=self.fixture();config={'native_route':r,'jobs':[{'ordered_modules':[]},j]}
  N.validate_prerequisite_order(config)
  config['jobs'][0]['ordered_modules']=['Fixture.Other']
  with self.assertRaisesRegex(ValueError,'exact reviewed arm delta'):N.validate_prerequisite_order(config)
 def test_runtime_rejects_unreviewed_native_order(self):
  v,r,c,j=self.fixture();runtime={'native_route':r,'ordered_modules':['Fixture.Tactic']}
  with self.assertRaisesRegex(ValueError,'repeat prerequisite'):N.runtime_body(runtime)
 def test_unrelated_unused_staged_source_is_allowed(self):
  v,r,c,j=self.fixture();c['proof_runtime']['module_files']['Unused.Hints']='Unused.v'
  files=[{'id':'module:'+row['module']+':source','sha256':row['sha256']} for row in v['source_inventory']]
  N.validate_closure({'native_route':r,'module_files':c['proof_runtime']['module_files']},v['target_import_closure'],files)
 def test_unreviewed_loaded_module_refuses(self):
  v,r,c,j=self.fixture();files=[{'id':'module:'+row['module']+':source','sha256':row['sha256']} for row in v['source_inventory']]
  with self.assertRaisesRegex(ValueError,'import closure'):N.validate_closure({'native_route':r,'module_files':c['proof_runtime']['module_files']},v['target_import_closure']+['Other.Hints'],files)
 def test_staged_source_resolving_to_other_hash_refuses(self):
  v,r,c,j=self.fixture();files=[{'id':'module:'+row['module']+':source','sha256':row['sha256']} for row in v['source_inventory']];files[0]['sha256']='0'*64
  with self.assertRaisesRegex(ValueError,'compiler-resolved'):N.validate_closure({'native_route':r,'module_files':c['proof_runtime']['module_files']},v['target_import_closure'],files)
 def test_production_umbrella_refuses_even_if_listed(self):
  v,r,c,j=self.fixture();v['target_import_closure'].append('ZesuSsz.Automation.All');r=self.js('leak.json',v)
  with self.assertRaisesRegex(ValueError,'excluded production'):N.authority(r)
 def test_arbitrary_tactic_text_refuses(self):
  with self.assertRaisesRegex(ValueError,'released commands'):N.body('idtac; admit.')
 def test_stock_parser_remains_exact(self):
  v,r,c,j=self.fixture('zesu_block2.')
  with self.assertRaisesRegex(ValueError,'native body changed'):S.source_statement(v['native_source']['path'])
  self.assertEqual(S.source_statement(v['native_source']['path'],'zesu_block2.')['native_body'],'zesu_block2.')
 def test_statement_change_refuses_independently(self):
  v,r,c,j=self.fixture();j['target']['statement_sha256']='0'*64
  with self.assertRaisesRegex(ValueError,'original declaration'):N.validate(r,workspace=self.root,modules=c['proof_runtime']['module_files'],target=j['target'],ordered=[])
 def test_historical_source_hash_cannot_replace_actual_source(self):
  v,r,c,j=self.fixture();j['target']['source_sha256']=v['original_source']['sha256']
  with self.assertRaisesRegex(ValueError,'reviewed source'):N.validate(r,workspace=self.root,modules=c['proof_runtime']['module_files'],target=j['target'],ordered=[])
 def test_return_reader_requires_exact_bound_body(self):
  v,r,c,j=self.fixture('zesu_block2.');log=self.js('CALLS.json',[{'tool':'rocq_check','arguments':{'body':'zesu_block.'},'result':{'success':True,'proof_finished':True}}])
  with self.assertRaisesRegex(ValueError,'exact native tactic'):A.annotate_native_return({'status':'passed'},log,r)
 def test_heldout_filter_removes_residual_and_source_details(self):
  result={'group_counts':{'active':1},'CPU':{'cpu_seconds':5},'aggregate_peak_bytes':10,'closure':'closed','release':'released','complete_state':'SECRET','private_residual':'SECRET','first_error':'SECRET'}
  with patch.object(H,'HELD_OUT',frozenset({'800d69b0'})):
   visible=H.summary('800d69b0',result,[{'sha256':'rule'}])
  self.assertNotIn('SECRET',json.dumps(visible))
  self.assertEqual(set(visible),{'block','held_out','group_counts','CPU','aggregate_peak_bytes','closure','release','frozen_rule_hashes'})
  self.assertIs(H.summary('800d69a4',result),result)
 def test_earlier_common_module_change_requires_new_prefix(self):
  import minimal_prefix
  v,r,c,j=self.fixture();v['prerequisite_delta']=['Fixture.Tactic']
  with self.assertRaisesRegex(ValueError,'new common prefix'):
   minimal_prefix.validate(v,self.root,c['proof_runtime']['module_files'])
 def test_changed_reused_object_refuses(self):
  v,r,c,j=self.fixture();(self.root/'Tactic.vo').write_text('changed')
  with self.assertRaisesRegex(ValueError,'input changed|compiled prefix'):
   N.validate(r,workspace=self.root,modules=c['proof_runtime']['module_files'],target=j['target'],ordered=[])
 def test_native_provider_compiles_no_dependencies_after_prefix(self):
  import entry_chain_provider as P
  v,r,c,j=self.fixture();exports=self.js('groups.json',{'kernel_groups':{'goals':[],'stack':[],'shelf':[],'given_up':[]}})
  runtime={'phase':'native','native_route':r,'ordered_modules':[],'target':{'block':j['target']},'module_files':c['proof_runtime']['module_files'],'mcp_argv':['unused']}
  rt=self.js('runtime.json',runtime);out=self.root/'native';out.mkdir();compile_files=[]
  class Raw:
   def __init__(self,data):self.structuredContent=data;self.isError=False
   def model_dump(self,**kwargs):return {'structuredContent':self.structuredContent}
  class Session:
   async def __aenter__(self):return self
   async def __aexit__(self,*args):pass
   async def initialize(self):pass
   async def call_tool(self,name,args):
    data={'success':True}
    if name in {'rocq_start','rocq_check'}:data.update(state_id=1,proof_finished=True)
    if name=='rocq_complete_goals':data.update(path=exports['path'],sha256=exports['sha256'])
    if name=='rocq_compile_file':
     compile_files.append(args['file']);Path(args['file']).with_suffix('.vo').write_text('native object')
    if name=='rocq_verify':data.update(verification_method='module_m',assumptions=[])
    return Raw(data)
  @asynccontextmanager
  async def streams(*args,**kwargs):yield (None,None)
  request={'runtime':rt['path'],'runtime_sha256':rt['sha256'],'workspace':str(self.root),'output':str(out),'identity':{}}
  groups={'goals':[],'stack':[],'shelf':[],'given_up':[]}
  with patch.object(P,'check_proof_bindings'),patch.object(P,'check_operation'),patch.object(P,'proof_environment',return_value={}),patch.object(P,'stdio_client',streams),patch.object(P,'ClientSession',lambda *a,**k:Session()),patch.object(P,'complete_groups',return_value=groups),patch('scratch_limits.record_search_origin'),patch('scratch_limits.record_search_end'):
   asyncio.run(P.execute(request))
  self.assertEqual(compile_files,[str(self.root/'Native.v')])
  calls=json.loads((out/'CALLS.json').read_text());self.assertEqual(sum(c['tool']=='rocq_compile_file' and c['arguments']['file'].endswith('Tactic.v') for c in calls),0)
  self.assertEqual(sum(c['tool']=='rocq_check' and c['arguments']['body']=='zesu_block.' for c in calls),1)

if __name__=='__main__':unittest.main()
