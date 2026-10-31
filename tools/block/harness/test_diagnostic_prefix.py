import copy,hashlib,json,sys,tempfile,unittest
from pathlib import Path
HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE/'code'))
import minimal_prefix as M
import memory_policy as P
class DiagnosticPrefix(unittest.TestCase):
 def setUp(self):
  self.temp=tempfile.TemporaryDirectory(dir='/home/cody/.cache/zesislar/shared-harness-tests');self.addCleanup(self.temp.cleanup);self.root=Path(self.temp.name);self.out=self.root/'jobs/prerequisites';self.out.mkdir(parents=True)
  self.job=P.apply_job({'phase':'prerequisites','output':str(self.out),'ordered_modules':[]})
  self.batch={'inside_pid':123,'inside_startticks':456,'aggregate_path':'/sys/fs/cgroup/owned'}
  self.runtime={'phase':'prerequisites','job_output':str(self.out),'ordered_modules':[],'canonical_admission':{'memory_job':self.job}}
  self.limits={'pid':123,'startticks':'456','effective_limits':{'memory.max':64*1024**3,'memory.swap.max':0}}
  self.prefix={'status':'passed','native_calls':0,'claim_bytes':24*1024**3,'fence_bytes':64*1024**3,'modules':[],'ready_runtime':self.write('READY.json',{'jobs':[self.job]})}
  self.prefix['closure']=self.write('jobs/prerequisites/CLOSURE.json',{'all_owned_actors_closed':True,'actors':[{'ended':True}],'claim_key':'x','batch_identity':self.batch});self.prefix['release']=self.write('jobs/prerequisites/RELEASE.json',{'released':True,'bytes':24*1024**3,'claim_key':'x'})
  self.prefix['fence_evidence']={'runtime':self.write('jobs/prerequisites/RUNTIME.json',self.runtime),'result':self.write('jobs/prerequisites/RESULT.json',{'success':True}),'client_limits':self.write('jobs/prerequisites/CLIENT-LIMITS.json',self.limits),'batch':self.write('jobs/prerequisites/BATCH-IDENTITY.json',self.batch)}
 def write(self,name,value):
  p=self.root/name;p.parent.mkdir(parents=True,exist_ok=True);p.write_text(json.dumps(value));return {'path':str(p),'sha256':hashlib.sha256(p.read_bytes()).hexdigest()}
 def check(self):return M.common(self.write('PREFIX.json',self.prefix))
 def test64_completed_physical_prefix_accepts(self):self.check()
 def test_historical24_prefix_stays_accepted(self):self.prefix['fence_bytes']=24*1024**3;del self.prefix['fence_evidence'];self.check()
 def test_missing_physical_evidence_refuses(self):del self.prefix['fence_evidence']['client_limits'];self.assertRaises(ValueError,self.check)
 def test_wrong_actual_limit_refuses(self):
  self.limits['effective_limits']['memory.max']=24*1024**3;self.prefix['fence_evidence']['client_limits']=self.write('jobs/prerequisites/CLIENT-LIMITS.json',self.limits);self.assertRaises(ValueError,self.check)
 def test_wrong_actor_refuses(self):
  self.limits['pid']=999;self.prefix['fence_evidence']['client_limits']=self.write('jobs/prerequisites/CLIENT-LIMITS.json',self.limits);self.assertRaises(ValueError,self.check)
 def test_wrong_job_policy_refuses(self):
  self.job['physical_fence_bytes']=24*1024**3;self.prefix['ready_runtime']=self.write('READY.json',{'jobs':[self.job]});self.assertRaises(ValueError,self.check)
 def test_inner_runtime_mismatch_refuses(self):
  self.runtime['ordered_modules']=['foreign'];self.prefix['fence_evidence']['runtime']=self.write('jobs/prerequisites/RUNTIME.json',self.runtime);self.assertRaises(ValueError,self.check)
 def test_foreign_receipt_refuses(self):
  self.prefix['fence_evidence']['client_limits']=self.write('foreign/CLIENT-LIMITS.json',self.limits);self.assertRaises(ValueError,self.check)
 def test_mutated_receipt_refuses(self):
  Path(self.prefix['fence_evidence']['client_limits']['path']).write_text('{}');self.assertRaises(ValueError,self.check)
 def test_unclosed_actors_refuse(self):
  self.prefix['closure']=self.write('jobs/prerequisites/CLOSURE.json',{'all_owned_actors_closed':False});self.assertRaises(ValueError,self.check)
 def test_unreleased_claim_refuses(self):
  self.prefix['release']=self.write('jobs/prerequisites/RELEASE.json',{'released':False});self.assertRaises(ValueError,self.check)
 def test_failed_completed_job_refuses(self):
  self.prefix['fence_evidence']['result']=self.write('jobs/prerequisites/RESULT.json',{'success':False});self.assertRaises(ValueError,self.check)
 def test_source_object_checks_remain_strict(self):
  self.prefix['modules']=[{'module':'Fixture','source':self.write('Source.v','bytes'),'object':self.write('Source.vo','object'),'receipt':self.write('RECEIPT.json',{'result':{'success':True},'source_sha256':'0'*64,'object_sha256':'0'*64})}];self.assertRaises(ValueError,self.check)
 def test_physical_evidence_enters_runtime_bindings(self):
  packet={'common_prefix':self.write('PREFIX.json',self.prefix)}
  rows=M.bindings(packet)
  for row in self.prefix['fence_evidence'].values():self.assertIn(row,rows)
if __name__=='__main__':unittest.main()
