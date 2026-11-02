"""Real cgroup controls for the actual scratch and entry-controller path."""
from pathlib import Path
import json,os,signal,subprocess,sys,tempfile,time,unittest
HERE=Path(__file__).resolve().parent
sys.path[:0]=[str(HERE/'code'),str(HERE),str(HERE.parents[2])]
from entry_chain import binding,save
from run_registry import identity,live,send_signal
from memory_policy import apply_job
DRIVER=HERE/'test-fixtures/controller-cleanup/driver.py'
TOOLS=HERE.parents[1]

class RealControllerCleanup(unittest.TestCase):
 def setUp(self):
  self.temp=tempfile.TemporaryDirectory(dir=os.environ.get('TMPDIR'));self.addCleanup(self.temp.cleanup)
  self.root=Path(self.temp.name).resolve();self.processes=[]
 def tearDown(self):
  for process in reversed(self.processes):
   actor=identity(process.pid)
   if actor and live(actor):send_signal(actor,signal.SIGTERM);send_signal(actor,signal.SIGCONT)
   try:process.wait(timeout=20)
   except subprocess.TimeoutExpired:self.fail('A disposable controller failed to close.')
 def wait_file(self,path,process):
  end=time.monotonic()+40
  while not path.is_file():
   if process.poll() is not None:self.fail('The fixture ended before '+str(path)+'; '+(self.root/'stderr').read_text())
   if time.monotonic()>end:self.fail('The fixture did not publish '+str(path))
   time.sleep(.02)
  return json.loads(path.read_text())
 def start(self,role,root,*args,environment=None):
  root.mkdir(parents=True,exist_ok=True)
  with (self.root/'stdout').open('ab') as out,(self.root/'stderr').open('ab') as err:
   process=subprocess.Popen([sys.executable,'-B',str(DRIVER),role,str(TOOLS),str(root),*map(str,args)],stdout=out,stderr=err,env=environment)
  self.processes.append(process);return process
 def config(self):
  out=self.root/'owned';out.mkdir();workspace=out/'prepared';workspace.mkdir()
  source=workspace/'Control.v';source.write_text('Lemma DesignedBoundary_control : True.\nProof.\nAbort.\n')
  target={'module':'Control','source_sha256':binding(source)['sha256']}
  entry=out/'entry.py';entry.write_text('import runpy,sys\nsys.argv=['+repr(str(DRIVER))+',"entry",'+repr(str(TOOLS))+','+repr(str(out))+']+sys.argv[1:]\nrunpy.run_path('+repr(str(DRIVER))+',run_name="__main__")\n')
  jobs=[apply_job({'phase':'prerequisites','key':'prerequisites','ordered_modules':['Fixture'],
       'target':target,'output':str(out/'jobs/prerequisites')}),
       apply_job({'phase':'native','key':'control','ordered_modules':[],'target':target,'output':str(out/'jobs/control')})]
  config={'prepared_workspace':str(workspace),'execution_released':True,'jobs':jobs,'bindings':[],
   'harness':{'fixture':True},'job_controller':binding(entry),'declarations_only':True,
   'proof_runtime':{'module_files':{'Control':'Control.v'}},'shared_latch':str(out/'latch'),
   'identity':{'fixture':'no-proof'},'admission':{'ledger':str(out/'LEDGER.json'),'lock':str(out/'LEDGER.lock')},
   'result_cache':{'purpose':'confirmation'},'source_overrides':[]}
  (out/'LEDGER.lock').touch();path=out/'RUNTIME.json';save(path,config)
  return out,path
 def foreign(self):
  out=self.root/'foreign';out.mkdir()
  env=dict(os.environ,ZESU_RUN_REGISTRY=str(out/'registry'),ZESU_RUN_REGISTRY_TOOL=str(TOOLS/'run_registry.py'))
  with (self.root/'stdout').open('ab') as stdout,(self.root/'stderr').open('ab') as stderr:
   process=subprocess.Popen([str(TOOLS/'resource_guard.sh'),'batch','fixture-foreign','--',sys.executable,'-B',str(DRIVER),'inside',str(TOOLS),str(out)],env=env,stdout=stdout,stderr=stderr)
  self.processes.append(process);self.wait_file(out/'READY.json',process)
  return process,json.loads((out/'BATCH-IDENTITY.json').read_text())
 def population(self,bound):
  path=Path(bound['aggregate_path'])
  if not path.exists():return '0'
  info=path.stat();self.assertEqual((info.st_dev,info.st_ino),(bound['aggregate_device'],bound['aggregate_inode']))
  return dict(line.split() for line in (path/'cgroup.events').read_text().splitlines())['populated']
 def control(self,signum=None,failure=False,pre_batch=False):
  foreign,foreign_bound=self.foreign();foreign_actor=identity(foreign.pid)
  out,path=self.config();env=dict(os.environ)
  if failure:env['FIXTURE_INJECT_FAILURE']='1'
  if pre_batch:env['FIXTURE_PRE_BATCH']='1'
  process=self.start('scratch',out,path,binding(path)['sha256'],environment=env)
  self.wait_file(out/'jobs/prerequisites/READY.json',process)
  bound=json.loads((out/'jobs/prerequisites/EARLY-AGGREGATE.json').read_text())
  self.assertEqual(self.population(bound),'1');self.assertEqual(self.population(foreign_bound),'1')
  if signum is not None:send_signal(identity(process.pid),signum)
  status=process.wait(timeout=75)
  self.assertEqual(status,128+signum if signum is not None else 1)
  self.assertEqual(self.population(bound),'0')
  self.assertTrue(live(foreign_actor));self.assertEqual(self.population(foreign_bound),'1')
  closure=json.loads((out/'jobs/prerequisites/CLOSURE.json').read_text())
  if pre_batch:
   self.assertFalse(closure['all_owned_actors_closed'])
   self.assertFalse((out/'jobs/prerequisites/RELEASE.json').exists())
  else:
   self.assertTrue(closure['all_owned_actors_closed'])
   self.assertTrue(json.loads((out/'jobs/prerequisites/RELEASE.json').read_text())['released'])
  self.assertTrue(json.loads((out/'CONTROLLER-EXIT-CLEANUP.json').read_text())['all_registered_children_closed'])
  print(json.dumps({'case':self.id(),'scratch_pid':process.pid,'exit_status':status,'owned_aggregate':bound,'owned_population_after':'0','foreign_aggregate':foreign_bound,'foreign_controller':foreign_actor,'foreign_population_after':'1','closure_confirmed':closure['all_owned_actors_closed'],'production_claims_created':False,'compiler_or_PET_started':False}),flush=True)
 def test_top_scratch_sigterm_closes_aggregate_and_preserves_foreign(self):self.control(signal.SIGTERM)
 def test_top_scratch_sigint_closes_aggregate_and_preserves_foreign(self):self.control(signal.SIGINT)
 def test_top_scratch_sighup_closes_aggregate_and_preserves_foreign(self):self.control(signal.SIGHUP)
 def test_top_scratch_failure_closes_aggregate_and_preserves_foreign(self):self.control(failure=True)
 def test_pre_batch_identity_cancellation_retains_unproven_claim(self):self.control(signal.SIGTERM,pre_batch=True)

if __name__=='__main__':unittest.main()
