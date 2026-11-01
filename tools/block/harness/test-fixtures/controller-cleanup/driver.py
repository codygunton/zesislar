"""Drive actual scratch/controller functions with synthetic, nonproof payloads.

Only fixture data preparation and admission are mocked. The stock guard,
controller launch, signal handling, cgroups, and closure/release checks are real.
"""
from pathlib import Path
import json,os,signal,subprocess,sys,time
role,tools,root,*args=sys.argv[1:]
tools=Path(tools);root=Path(root);here=tools/'block/harness'
sys.path[:0]=[str(here/'code'),str(here),str(tools/'block'),str(tools)]
from entry_chain import binding,save
from check_entry_outside import ticks
GUARD=tools/'resource_guard.sh'
SELF=Path(__file__).resolve()

if role=='sleeper':
 save(root/(args[0]+'.json'),{'pid':os.getpid(),'startticks':ticks(os.getpid())})
 while True:time.sleep(1)
elif role=='inside':
 from aggregate_layout import aggregate_root
 group=aggregate_root();info=group.stat()
 identity={'aggregate_path':str(group),'aggregate_device':info.st_dev,'aggregate_inode':info.st_ino,
           'inside_pid':os.getpid(),'inside_startticks':ticks(os.getpid())}
 save(root/'EARLY-AGGREGATE.json',identity)
 if os.environ.get('FIXTURE_PRE_BATCH')=='1':
  save(root/'READY.json',{'pre_batch':True})
  while True:time.sleep(1)
 save(root/'BATCH-IDENTITY.json',identity)
 children=[]
 for name in ['client','pet']:
  children.append(subprocess.Popen([str(GUARD),'scope','fixture-'+name,'--',sys.executable,'-B',str(SELF),'sleeper',str(tools),str(root),name]))
 deadline=time.monotonic()+30
 while not all((root/(name+'.json')).is_file() for name in ['client','pet']):
  if time.monotonic()>deadline:raise RuntimeError('Fixture scopes did not start.')
  time.sleep(.02)
 save(root/'READY.json',{'synthetic':True,'proof_or_compiler':False})
 while True:time.sleep(1)
elif role=='entry':
 import entry_chain_run as E,restart_bindings
 # No fake proof/object reaches a real validator or compiler. These fixture
 # callbacks replace only metadata setup and its private reservation boundary.
 restart_bindings.verify_restart_runtime=lambda *a,**k:True
 E.check_proof_bindings=lambda *a,**k:None
 def stage(config,job,out):
  workspace=out/'workspace';workspace.mkdir()
  return {'bindings':[]},workspace
 E.stage_job=stage
 E.outer_argv=lambda workspace,key,out:[str(GUARD),'batch','fixture-'+key,'--',sys.executable,'-B',str(SELF),'inside',str(tools),str(out)]
 clean=E.clean_environment
 def environment():
  result=clean();result.update(ZESU_RUN_REGISTRY=str(root/'registry'),ZESU_RUN_REGISTRY_TOOL=str(tools/'run_registry.py'))
  if os.environ.get('FIXTURE_PRE_BATCH'):result['FIXTURE_PRE_BATCH']=os.environ['FIXTURE_PRE_BATCH']
  return result
 E.clean_environment=environment
 def reserve(policy,key,owner,receipt,**kwargs):
  kwargs['recheck']()
  save(Path(policy['ledger']),{'fixed_claims':{key:policy['minimum_claim_bytes']},'entry_pilot_outside_owners':{key:owner}})
  save(receipt,[{'admitted':True,'synthetic_private_ledger':True,'owner':owner,'claim_key':key}])
 E.reserve=reserve
 sys.argv=[str(tools/'block/harness/code/entry_chain_run.py'),*args]
 raise SystemExit(E.main())
elif role=='scratch':
 import scratch,restart_bindings,end_run_cleanup
 restart_bindings.verify_restart_runtime=lambda *a,**k:True
 scratch.check_proof_bindings=lambda *a,**k:None
 end_run_cleanup.finish=lambda *a,**k:None
 if os.environ.get('FIXTURE_INJECT_FAILURE')=='1':
  import controller_cleanup as C
  def failure(argv,**kwargs):
   C.launch(argv,**kwargs)
   deadline=time.monotonic()+30
   while not (root/'jobs/prerequisites/READY.json').is_file():
    if time.monotonic()>deadline:raise RuntimeError('Fixture aggregate did not start.')
    time.sleep(.02)
   raise RuntimeError('Injected scratch controller failure.')
  C.run=failure
 raise SystemExit(scratch.execute(args[0],args[1]))
else:raise ValueError('Unknown fixture role.')
