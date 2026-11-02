"""The explicit control-peak route preserves default sizing and exact boundaries."""
import copy,hashlib,json,sys,tempfile,unittest
from pathlib import Path
from unittest.mock import patch
HERE=Path(__file__).resolve().parent
sys.path[:0]=[str(HERE/'code'),str(HERE.parent)]
import measured_focused as measured
import memory_policy as memory

class CompletedControlPeakTests(unittest.TestCase):
 def setUp(self):
  tmp=tempfile.TemporaryDirectory();self.addCleanup(tmp.cleanup);root=Path(tmp.name);workspace=root/'workspace';workspace.mkdir();source=workspace/'Control.v';source.write_text('Goal True. Proof. exact I. Qed.\n')
  def save(name,value):
   path=root/name;path.parent.mkdir(parents=True,exist_ok=True);path.write_text(json.dumps(value));return {'path':str(path),'sha256':hashlib.sha256(path.read_bytes()).hexdigest()}
  source_ref={'path':str(source),'sha256':hashlib.sha256(source.read_bytes()).hexdigest()};module='Example.Control';old={'module':module,'steps':[{'body':'iSteps.'}]};new={'module':module,'steps':[{'body':'repeat liStep.'}]};compiler={'path':'/pinned/coqc','sha256':'c'*64};job={'key':'prerequisites','phase':'prerequisites','ordered_modules':[],'target':{'module':module}}
  self.prior={'prepared_workspace':str(workspace),'proof_runtime':{'module_files':{module:'Control.v'}},'bindings':[source_ref],'physical_flags':['-Q',str(workspace),'Example'],'control_session':old,'effective_compiler_version':{'compiler':compiler},'declarations_only':True,'jobs':[job]}
  cpu={'aggregate_peak_bytes':6954352640,'CPU_budget_enforced':False,'final_memory_accounting_available':True,'memory_events':{'available':True,'counters':{'max':0,'oom':0,'oom_kill':0,'oom_group_kill':0}}};key='claim';directory=root/'job'
  self.m={'accounting':save('job/CPU-FINAL.json',cpu),'completed_failed_run':save('job/RESULT.json',{'phase':'prerequisites','status':'infrastructure_failed','returncode':1,'CPU':cpu,'aggregate_peak_bytes':6954352640}),'closure':save('job/CLOSURE.json',{'all_owned_actors_closed':True,'actors':[{'ended':True}],'claim_key':key}),'release':save('job/RELEASE.json',{'released':True,'claim_key':key,'bytes':64*1024**3}),'calls':save('CALLS.json',[]),'profile_origin':save('old-profile.json',{'sources':[]}),'session':save('session.json',new),'subject':source_ref,'peak_bytes':6954352640,'claim_bytes':10431528960,'physical_fence_bytes':64*1024**3}
  self.authority={'schema':'scratch.completed-control-peak-authority.v1','measurement':save('measurement.json',self.m),'prior_runtime':save('runtime.json',self.prior),'prior_job_runtime':save('job/RUNTIME.json',{'phase':'prerequisites','physical_compiler':compiler,'control_session':old,'job_output':str(directory),'ordered_modules':[]}), 'prior_control_session':old,'current_control_session':new,'source_module':module,'source_sha256':source_ref['sha256']}
  auth=save('authority.json',self.authority);mock=patch.object(measured,'POLICY_SHA',auth['sha256']);mock.start();self.addCleanup(mock.stop)
  self.profile={'schema':'scratch.admission-profile.v1','kind':'focused_check','sources':[],'memory_booking':measured.BOOKING,'completed_control_peak':auth,'control_source':dict(source_ref,module=module,role='consumer_check')}
  self.config=copy.deepcopy(self.prior);self.config['control_session']=copy.deepcopy(new)
 def test_exact_completed_error_claim(self):
  self.assertEqual(measured.claim(self.profile,self.config),10431528960)
 def test_changed_comparison_refuses(self):
  self.config['control_session']['steps'][-1]['body']='iSteps.'
  with self.assertRaisesRegex(ValueError,'transition'):measured.claim(self.profile,self.config)
 def test_other_source_refuses(self):
  self.profile['control_source']['sha256']='0'*64
  with self.assertRaisesRegex(ValueError,'source boundary'):measured.claim(self.profile,self.config)
 def test_changed_compiler_refuses(self):
  self.config['effective_compiler_version']['compiler']['sha256']='0'*64
  with self.assertRaisesRegex(ValueError,'compiler'):measured.claim(self.profile,self.config)
 def test_changed_flags_refuses(self):
  self.config['physical_flags'].append('-unsafe')
  with self.assertRaisesRegex(ValueError,'flags'):measured.claim(self.profile,self.config)
 def test_unapproved_accounting_authority_refuses(self):
  self.profile['completed_control_peak']['sha256']='0'*64
  with self.assertRaisesRegex(ValueError,'not approved'):measured.claim(self.profile,self.config)
 def changed(self,key,change):
  original=measured.read
  def read(ref):
   value=copy.deepcopy(original(ref))
   if ref==self.m[key]:change(value)
   return value
  return patch.object(measured,'read',side_effect=read)
 def test_oom_refuses(self):
  def bad(x):x['memory_events']['counters']['oom']=1
  with self.changed('accounting',bad),self.assertRaises(ValueError):measured.claim(self.profile,self.config)
 def test_missing_final_accounting_refuses(self):
  with self.changed('accounting',lambda x:x.update(final_memory_accounting_available=False)),self.assertRaises(ValueError):measured.claim(self.profile,self.config)
 def test_cpu_cap_refuses(self):
  with self.changed('accounting',lambda x:x.update(CPU_budget_enforced=True)),self.assertRaises(ValueError):measured.claim(self.profile,self.config)
 def test_open_actors_refuse(self):
  with self.changed('closure',lambda x:x.update(all_owned_actors_closed=False)),self.assertRaisesRegex(ValueError,'lifecycle'):measured.claim(self.profile,self.config)
 def test_unreleased_claim_refuses(self):
  with self.changed('release',lambda x:x.update(released=False)),self.assertRaisesRegex(ValueError,'lifecycle'):measured.claim(self.profile,self.config)
 def test_public_workload_roundtrip(self):
  with tempfile.TemporaryDirectory() as tmp:
   path=Path(tmp)/'profile.json';path.write_text(json.dumps(self.profile));ref={'path':str(path),'sha256':hashlib.sha256(path.read_bytes()).hexdigest()}
   job=dict(self.prior['jobs'][0],ordered_modules=[])
   workload=memory.workload_for_job(ref,job,self.config);selected=memory.apply_job(job,workload=workload)
   self.assertEqual(selected['claim_bytes'],10431528960);self.assertEqual(selected['physical_fence_bytes'],64*1024**3)
   self.assertEqual(memory.validate_job(selected),10431528960)
 def test_expanded_compile_boundary_refuses(self):
  with self.assertRaisesRegex(ValueError,'compile boundary'):measured.claim(self.profile,self.config,['Other.Module'])
 def test_default_unchanged(self):
  with tempfile.TemporaryDirectory() as tmp:
   self.profile.pop('memory_booking');self.profile.pop('completed_control_peak');self.profile.pop('control_source')
   path=Path(tmp)/'profile.json';path.write_text(json.dumps(self.profile));ref={'path':str(path),'sha256':hashlib.sha256(path.read_bytes()).hexdigest()};job=dict(self.prior['jobs'][0],ordered_modules=[])
   workload=memory.workload_for_job(ref,job,self.config);self.assertEqual(memory.apply_job(job,workload=workload)['claim_bytes'],8*1024**3)
if __name__=='__main__':unittest.main()
