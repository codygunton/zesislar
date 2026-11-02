"""Closed failed runs authorize only their exact successful individual receipts."""
import copy,json,sys,tempfile,unittest
from pathlib import Path
from unittest.mock import patch
HERE=Path(__file__).resolve().parent
sys.path[:0]=[str(HERE/'code'),str(HERE.parent),str(HERE.parents[1])]
from entry_chain import binding,read_bound
import closed_compilation_origin as C

class ClosedOriginTests(unittest.TestCase):
 def setUp(self):
  t=tempfile.TemporaryDirectory();self.addCleanup(t.cleanup);self.root=Path(t.name);self.job=self.root/'job';self.workspace=self.job/'workspace';self.workspace.mkdir(parents=True)
  self.source=self.workspace/'Owner.v';self.source.write_text('(* Fixture declaration. *)\n');self.obj=self.source.with_suffix('.vo');self.obj.write_bytes(b'owned object fixture');self.module='Example.Owner';self.comp=self.root/'coqc';self.comp.write_bytes(b'pinned compiler');self.compiler=binding(self.comp);dep=self.root/'coqdep';dep.write_bytes(b'pinned resolver');self.flags=['-Q',str(self.workspace),'Example'];self.producer={'pid':99999999,'startticks':1,'uid':1000}
  graph=self.save('graph.json',{'import_edges':[]});inventory=self.save('inventory.json',{'bindings':[self.compiler,binding(dep),binding(self.source)]})
  self.inner=self.save('job/RUNTIME.json',{'job_output':str(self.job),'physical_compiler':self.compiler,'binding_inventory':inventory,'cache_import_graph':graph,'module_files':{self.module:'Owner.v'},'physical_flags':self.flags,'canonical_admission':{'minimum_claim_bytes':64*1024**3}})
  outer=self.save('outer.json',{'prepared_workspace':str(self.root/'seed'),'proof_runtime':{'module_files':{self.module:'Owner.v'}},'physical_flags':['-Q',str(self.root/'seed'),'Example']})
  self.snapshot=self.save('snapshot.json',{'runtime':self.inner,'compiler':self.compiler,'producer':self.producer,'mapping_context':{'flags':self.flags}})
  validation=self.save('validation.json',{'snapshot':self.snapshot,'directly_hashed_inputs':[],'import_selection':{'module':self.module,'owned_workspace':str(self.workspace),'source':binding(self.source),'graph':graph,'imported_objects':[]}})
  argv=[self.compiler['path'],*self.flags,str(self.source)];inputs=self.save('input.json',{'source':binding(self.source),'compiler':self.compiler,'owned_workspace':str(self.workspace),'physical_argv':argv,'validation':{'snapshot':self.snapshot}})
  self.physical=self.save('physical.json',{'input':inputs,'physical_argv':argv,'returncode':0,'output_validation':{'success':True},'output_capture':{'complete':True},'compiler_outputs':{'object':{'binding':binding(self.obj)}},'input_validation':validation})
  self.receipt=self.save('receipt.json',{'runtime':self.inner,'snapshot':self.snapshot,'producer':self.producer,'source':binding(self.source),'object':binding(self.obj),'compiler':self.compiler,'normalized_flags':self.flags,'successful_compilation':True,'tool_result':{'success':True},'physical_result':self.physical,'import_provenance':{'schema':'entry-chain.object-imports.v1','module':self.module,'owned_workspace':str(self.workspace),'compiler':self.compiler,'normalized_flags':['-Q','{workspace}','Example'],'validation':validation,'imported_objects':[]}})
  index=self.save('index.json',{'index':{'runtime':self.inner,'snapshot':self.snapshot,'producer':self.producer,'receipts':[self.receipt]},'mac':'bound fixture index'})
  cpu={'aggregate_peak_bytes':1};account=self.save('job/CPU-FINAL.json',cpu);result=self.save('job/RESULT.json',{'success':False,'phase':'prerequisites','CPU':cpu,'aggregate_peak_bytes':1});batch=self.save('job/BATCH-IDENTITY.json',{'aggregate_path':str(self.root/'absent-aggregate')});self.closure=self.save('job/CLOSURE.json',{'owner':self.producer,'actors':[dict(self.producer,ended=True)],'all_owned_actors_closed':True,'batch_identity':read_bound(batch),'claim_key':'claim'});release=self.save('job/RELEASE.json',{'released':True,'bytes':64*1024**3,'claim_key':'claim'});final=self.save('final.json',{'runtime_sha256':self.inner['sha256'],'final_validation':{'success':True,'proof_bindings_checked':1}})
  self.value={'schema':'entry-chain.closed-compilation-origin.v1','kind':C.KIND,'outer_runtime':outer,'inner_runtime':self.inner,'binding_inventory':inventory,'accepted_object_index':index,'compiler_snapshot':self.snapshot,'import_graph':graph,'compiler':self.compiler,'coqdep':binding(dep),'object_workspace':str(self.workspace),'successful_modules':[{'module':self.module,'receipt':self.receipt,'source':binding(self.source),'object':binding(self.obj),'physical_result':self.physical,'publication':None}],'failed_result':result,'CPU_final':account,'final_validation':final,'closure':self.closure,'release':release,'batch_identity':batch}
  self.reference=self.save('origin.json',self.value);self.authority={'kind':C.KIND,'binding':self.reference,'module_receipts':{self.module:self.receipt}}
 def save(self,name,value):
  p=self.root/name;p.parent.mkdir(parents=True,exist_ok=True);p.write_text(json.dumps(value));return binding(p)
 def context(self):return C.context(self.authority,self.reference,read_bound)
 def selected(self):return C.selected_origin(self.authority,self.reference,self.module,self.source,self.obj,self.compiler,self.flags,self.workspace,read_bound)
 def change_origin(self,key,value):
  self.value[key]=value;self.reference=self.save('origin.json',self.value);self.authority['binding']=self.reference
 def test_exact_individual_compilation_passes(self):
  accepted,_=self.selected();self.assertEqual(accepted['kind'],C.LABEL);self.assertNotIn('ready',accepted)
 def test_existing_migration_schema_roundtrip(self):
  import object_import_migration as M
  policy=self.save('policy.json',{'origins':[self.authority],'inspector_build':{'path':'fixture-inspector','sha256':'i'*64}})
  comparison={'objects':[],'checks':[]}
  with patch.object(M,'POLICY',Path(policy['path'])),patch.object(M,'comparisons',return_value=([],comparison)):
   value=M.create(self.reference,self.module,self.source,self.obj,self.compiler,self.flags,self.workspace)
   self.assertEqual(value['schema'],'entry-chain.object-import-migration.v1')
   self.assertEqual(value['origin']['kind'],C.LABEL)
   ref=self.save('migration.json',value);imports,workspace=M.validate(ref,self.module,self.source,self.obj,self.compiler,self.flags,self.workspace)
   self.assertEqual(imports,{});self.assertEqual(workspace,self.workspace)
 def test_unlisted_origin_refuses(self):
  self.authority['binding']={'path':'elsewhere','sha256':'0'*64}
  with self.assertRaisesRegex(ValueError,'not authorized'):self.context()
 def test_workspace_mismatch_refuses(self):
  self.change_origin('object_workspace',str(self.root/'other'))
  with self.assertRaisesRegex(ValueError,'workspace'):self.context()
 def test_inventory_mismatch_refuses(self):
  self.change_origin('binding_inventory',self.save('other-inventory.json',{'bindings':[]}))
  with self.assertRaisesRegex(ValueError,'inventory'):self.context()
 def test_compiler_mismatch_refuses(self):
  self.change_origin('compiler',dict(self.compiler,sha256='0'*64))
  with self.assertRaisesRegex(ValueError,'compiler context'):self.context()
 def test_incomplete_receipt_set_refuses(self):
  self.authority['module_receipts']={}
  with self.assertRaisesRegex(ValueError,'exact authorized receipts'):self.context()
 def test_absent_module_refuses(self):
  with self.assertRaisesRegex(ValueError,'lacks an authorized'):C.selected_origin(self.authority,self.reference,'Other',self.source,self.obj,self.compiler,self.flags,self.workspace,read_bound)
 def test_failed_individual_receipt_refuses(self):
  original=read_bound
  def read(ref):
   value=copy.deepcopy(original(ref))
   if ref==self.receipt:value['successful_compilation']=False
   return value
  with self.assertRaisesRegex(ValueError,'incomplete'):C.selected_origin(self.authority,self.reference,self.module,self.source,self.obj,self.compiler,self.flags,self.workspace,read)
 def test_failed_physical_record_refuses(self):
  value=read_bound(self.physical);value['returncode']=1;Path(self.physical['path']).write_text(json.dumps(value))
  with self.assertRaises(ValueError):self.selected()
 def test_changed_object_refuses(self):
  self.obj.write_bytes(b'changed object')
  with self.assertRaises(ValueError):self.selected()
 def test_changed_graph_refuses(self):
  self.change_origin('import_graph',self.save('other-graph.json',{'import_edges':[]}))
  with self.assertRaisesRegex(ValueError,'context'):self.context()
 def test_open_actor_refuses(self):
  value=read_bound(self.closure);value['all_owned_actors_closed']=False;self.change_origin('closure',self.save('job/CLOSURE.json',value))
  with self.assertRaisesRegex(ValueError,'lifecycle'):self.context()
if __name__=='__main__':unittest.main()
