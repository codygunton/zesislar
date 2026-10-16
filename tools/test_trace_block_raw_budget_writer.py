import concurrent.futures, importlib.util, json, multiprocessing, os, subprocess, sys, tempfile, unittest
from pathlib import Path
SOURCE=Path(__file__).resolve().parent/'block/trace_block_raw_budget.py'
spec=importlib.util.spec_from_file_location('budget',SOURCE);b=importlib.util.module_from_spec(spec);spec.loader.exec_module(b)
def reserve_child(args):
 ledger,path=args
 try:b.RawBudget(ledger).write(path,[b'x'*100]);return True
 except b.BudgetExceeded:return False
class BudgetTests(unittest.TestCase):
 def setUp(self):
  self.tmp=tempfile.TemporaryDirectory();self.root=Path(self.tmp.name);self.b=b.RawBudget.create(self.root,limit=12000,control_reserve=1000)
 def tearDown(self):self.tmp.cleanup()
 def check_bound(self):
  value=self.b.read();actual=sum(p.stat().st_size for p in self.root.rglob('*')if p.is_file())
  self.assertLessEqual(actual,value['used_bytes']);self.assertLessEqual(value['used_bytes'],12000)
  self.assertEqual(self.b.ledger.stat().st_size,8192);return value
 def test_maximum(self):
  for limit in [2000000001, True, 3.0, 8192]:
   with self.subTest(limit=limit),tempfile.TemporaryDirectory()as directory:
    with self.assertRaises(ValueError):b.RawBudget.create(directory,limit=limit,control_reserve=1)
    self.assertFalse((Path(directory)/'evidence/RAW-BUDGET.json').exists())
 def test_reserve_bounds(self):
  for reserve in [-1,True,12000]:
   with self.subTest(reserve=reserve),tempfile.TemporaryDirectory()as directory:
    with self.assertRaises(ValueError):b.RawBudget.create(directory,limit=12000,control_reserve=reserve)
 def test_drain_after_denial(self):
  code="import subprocess,sys; p=subprocess.Popen(sys.argv[1:],stdin=subprocess.PIPE); p.stdin.write(b'x'*4000000); p.stdin.close(); raise SystemExit(p.wait())"
  result=subprocess.run([sys.executable,'-c',code,sys.executable,str(SOURCE),'--ledger',str(self.b.ledger),'--destination',str(self.root/'stream')],capture_output=True)
  self.assertEqual(result.returncode,75);self.assertEqual(result.stderr,b'');self.check_bound()
 def test_drain_after_file_error(self):
  (self.root/'existing').write_bytes(b'original')
  code="import subprocess,sys; p=subprocess.Popen(sys.argv[1:],stdin=subprocess.PIPE); p.stdin.write(b'x'*4000000); p.stdin.close(); raise SystemExit(p.wait())"
  result=subprocess.run([sys.executable,'-c',code,sys.executable,str(SOURCE),'--ledger',str(self.b.ledger),'--destination',str(self.root/'existing')],capture_output=True)
  self.assertEqual(result.returncode,74);self.assertEqual(result.stderr,b'');self.assertEqual((self.root/'existing').read_bytes(),b'original')
 def test_directory_link_writer(self):
  (self.root/'alias').symlink_to(self.root.parent,target_is_directory=True)
  old=os.environ.get('ZESU_TRACE_RAW_BUDGET');os.environ['ZESU_TRACE_RAW_BUDGET']=str(self.b.ledger)
  try:
   with self.assertRaises(ValueError):b.from_environment(self.root/'alias/outside')
  finally:
   if old is None:os.environ.pop('ZESU_TRACE_RAW_BUDGET')
   else:os.environ['ZESU_TRACE_RAW_BUDGET']=old
 def test_seed(self):self.assertEqual(self.b.read()['used_bytes'],8192)
 def test_data_denial_and_control(self):
  self.b.write(self.root/'data',[b'x'*2800])
  with self.assertRaises(b.BudgetExceeded):self.b.write(self.root/'counter',[b'x'*9])
  with self.assertRaises(b.BudgetExceeded):self.b.write(self.root/'error',[b'x'])
  self.b.write(self.root/'SESSION.json',[b'{}'],control=True)
  self.assertFalse(self.check_bound()['complete'])
 def test_control_denial(self):
  with self.assertRaises(b.BudgetExceeded):self.b.write(self.root/'SESSION.json',[b'x'*4000],control=True)
  self.assertFalse(self.check_bound()['complete'])
 def test_partial_prefix(self):
  with self.assertRaises(b.BudgetExceeded):self.b.write(self.root/'capture',[b'a'*2000,b'b'*2000])
  self.assertEqual((self.root/'capture').read_bytes(),b'a'*2000);self.check_bound()
 def test_sticky(self):
  with self.assertRaises(b.BudgetExceeded):self.b.reserve(self.root/'a',sys.maxsize)
  with self.assertRaises(b.BudgetExceeded):self.b.reserve(self.root/'b',0)
  self.assertEqual(self.check_bound()['denied_writes'],2)
 def test_overflow_path(self):
  path=self.root/('\u0001'*200)/('\u2603'*200)/('\U0001f680'*200)
  with self.assertRaises(b.BudgetExceeded):self.b.reserve(path,sys.maxsize)
  value=self.check_bound();self.assertLessEqual(len(value['first_denial']['path'].encode()),512)
 def test_bad_count(self):
  for count in [-1,True,1.0,sys.maxsize+1]:
   with self.subTest(count=count),self.assertRaises(ValueError):self.b.reserve(self.root/'x',count)
 def test_outside(self):
  with self.assertRaises(ValueError):self.b.reserve(self.root.parent/'outside',1)
  with self.assertRaises(ValueError):self.b.reserve(self.b.ledger,1)
 def test_alias(self):
  (self.root/'alias').symlink_to(self.root.parent,target_is_directory=True)
  with self.assertRaises(ValueError):self.b.reserve(self.root/'alias/outside',1)
 def test_no_replace(self):
  (self.root/'existing').write_bytes(b'original')
  with self.assertRaises(FileExistsError):self.b.write(self.root/'existing',[b'changed'])
  self.assertEqual((self.root/'existing').read_bytes(),b'original')
 def test_threads(self):
  with concurrent.futures.ThreadPoolExecutor(max_workers=16)as pool:
   results=list(pool.map(reserve_child,[(self.b.ledger,self.root/str(i))for i in range(80)]))
  self.assertEqual(sum(results),28);self.assertFalse(self.check_bound()['complete'])
 def test_processes(self):
  with multiprocessing.get_context('fork').Pool(8)as pool:
   results=pool.map(reserve_child,[(self.b.ledger,self.root/str(i))for i in range(80)])
  self.assertEqual(sum(results),28);self.assertFalse(self.check_bound()['complete'])
 def test_cli_stdout(self):self.pipe('reader.stdout')
 def test_cli_stderr(self):self.pipe('reader.stderr')
 def pipe(self,name):
  result=subprocess.run([sys.executable,str(SOURCE),'--ledger',str(self.b.ledger),'--destination',str(self.root/name)],input=b'x'*20000,capture_output=True)
  self.assertEqual(result.returncode,75);self.assertEqual(result.stdout,b'');self.assertEqual(result.stderr,b'');self.check_bound()
 def test_bootstrap_existing(self):
  with tempfile.TemporaryDirectory()as directory:
   root=Path(directory);(root/'input').write_bytes(b'x'*13)
   budget=b.RawBudget.create(root,limit=10000,control_reserve=100)
   self.assertEqual(budget.read()['used_bytes'],8205)
 def test_bootstrap_denied(self):
  with tempfile.TemporaryDirectory()as directory:
   with self.assertRaises(ValueError):b.RawBudget.create(directory,limit=8193,control_reserve=1)
   self.assertFalse((Path(directory)/'evidence/RAW-BUDGET.json').exists())


import hashlib,importlib.util,json,os,sys,tempfile,unittest
from pathlib import Path
from unittest.mock import patch
B=Path(__file__).resolve().parent/'block'
sys.path.insert(0,str(B))
import trace_block_mcp as backend
class FirstRawTests(unittest.TestCase):
 def setUp(self):
  self.tmp=tempfile.TemporaryDirectory();self.root=Path(self.tmp.name);self.workspace=self.root/'workspace';self.workspace.mkdir()
  self.helper=self.workspace/'writer.py';self.helper.write_bytes((B/'trace_block_raw_budget.py').read_bytes())
  self.request={'workspace':str(self.workspace),'writer_id':'worker2-a','observer_runtime':{'raw_policy':'trigger-selected-raw-v2','raw_budget_writer':{'path':str(self.helper),'sha256':hashlib.sha256(self.helper.read_bytes()).hexdigest(),'bytes':self.helper.stat().st_size}}}
  self.out=self.root/'raw';self.env=patch.dict(os.environ,{},clear=False);self.env.start();os.environ.pop('ZESU_TRACE_RAW_BUDGET',None)
 def tearDown(self):self.env.stop();self.tmp.cleanup()
 def test_first_write(self):
  real=backend.budget_write_bytes;writes=[]
  def write(path,payload,**kw):
   ledger=self.out/'evidence/RAW-BUDGET.json'
   self.assertTrue(ledger.is_file());self.assertEqual(ledger.stat().st_size,8192)
   writes.append(Path(path).name);return real(path,payload,**kw)
  def run(command,**kw):
   env=kw['env'];self.assertEqual(env['ZESU_TRACE_RAW_BUDGET'],str(self.out/'evidence/RAW-BUDGET.json'))
   self.assertEqual(writes,['REQUEST.json','ADMISSION-REQUEST.json'])
   backend.save_json(self.out/'evidence/CAPTURE.json',{'error':None})
   return type('Return',(),{'returncode':0})()
  with patch.object(backend,'budget_write_bytes',side_effect=write),patch.object(backend.subprocess,'run',side_effect=run),patch.dict(os.environ,{'ZESU_MCP_PYTHON':sys.executable}):
   self.assertEqual(backend.run_capture(self.request,self.out),{'error':None})
  self.assertEqual(writes,['REQUEST.json','ADMISSION-REQUEST.json','CAPTURE.json'])
 def test_attach_identity(self):
  first,_=backend.prepare_raw_budget(self.request,self.out);inode=first.ledger.stat().st_ino
  backend.save_json(self.out/'evidence/REQUEST.json',self.request)
  other,_=backend.prepare_raw_budget(self.request,self.out)
  self.assertEqual(other.ledger.stat().st_ino,inode);self.assertGreater(other.read()['used_bytes'],8192)
 def test_preexisting(self):
  self.out.mkdir();(self.out/'unexpected').write_bytes(b'x')
  with self.assertRaises(ValueError):backend.prepare_raw_budget(self.request,self.out)
  self.assertFalse((self.out/'evidence/RAW-BUDGET.json').exists())
 def test_wrong_owner(self):
  first,_=backend.prepare_raw_budget(self.request,self.out);os.environ['ZESU_TRACE_RAW_BUDGET']='other'
  with self.assertRaises(ValueError):backend.prepare_raw_budget(self.request,self.out)
 def test_unaccounted(self):
  first,_=backend.prepare_raw_budget(self.request,self.out);(self.out/'unreserved').write_bytes(b'x')
  with self.assertRaises(ValueError):backend.prepare_raw_budget(self.request,self.out)
 def test_link(self):
  first,_=backend.prepare_raw_budget(self.request,self.out);(self.out/'link').symlink_to(self.workspace,target_is_directory=True)
  with self.assertRaises(ValueError):backend.prepare_raw_budget(self.request,self.out)
if __name__=='__main__':unittest.main()
