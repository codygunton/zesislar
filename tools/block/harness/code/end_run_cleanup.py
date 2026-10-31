"""Remove ended-run compiled copies. Retain all evidence and sources."""
from pathlib import Path
import hashlib,json,os,re,stat,time

MINIMUM_BYTES=1_000_000
ARTIFACT_SUFFIXES=frozenset({'.vo','.vos','.vok','.glob','.cmxs','.cmi','.cmo','.cmx','.cma','.cmxa','.o','.a','.so'})


def policy(enabled=True):
 if type(enabled) is not bool:raise ValueError('The cleanup setting must be Boolean.')
 return {'schema':'scratch.end-run-cleanup.v1','enabled':enabled}


def binding(path):
 path=Path(path)
 return {'path':str(path),'sha256':hashlib.sha256(path.read_bytes()).hexdigest()}


def load(path):return json.loads(Path(path).read_text())


def write_once(path,data):
 path=Path(path);temporary=path.with_name(path.name+'.tmp-'+str(os.getpid()))
 with temporary.open('x') as stream:
  json.dump(data,stream,indent=2);stream.write('\n')
 try:os.link(temporary,path)
 finally:temporary.unlink()


def actor_alive(actor):
 try:
  fields=Path('/proc',str(actor['pid']),'stat').read_text().rsplit(')',1)[1].split()
  return int(fields[19])==int(actor['startticks'])
 except FileNotFoundError:return False


def contained(root,path):
 root=Path(root);path=Path(path)
 if not path.is_absolute() or not path.is_relative_to(root) or path.resolve()!=path:raise ValueError('A cleanup path leaves its owned run or is not canonical.')
 cursor=path
 while cursor!=root:
  if cursor.is_symlink():raise ValueError('A cleanup path crosses a symbolic link.')
  cursor=cursor.parent
 if root.is_symlink() or root.resolve()!=root:raise ValueError('The cleanup root contains a symbolic link.')
 return path


def closed_job(job,out):
 directory=contained(out,Path(job['output']))
 if directory!=out/'jobs'/job['key']:raise ValueError('A cleanup job is outside its exact owned directory.')
 started=any((directory/name).exists() for name in ['STARTED.json','workspace','RESULT.json','BATCH-PROCESS.json'])
 if not started:return None
 result=directory/'RESULT.json';closure=directory/'CLOSURE.json';release=directory/'RELEASE.json'
 if not all(p.is_file() for p in [result,closure,release]):raise ValueError('A started job lacks its sealed result or lifecycle receipts.')
 c=load(closure);r=load(release)
 if c.get('all_owned_actors_closed') is not True or any(a.get('ended') is not True or actor_alive(a) for a in c.get('actors',[])):
  raise ValueError('An owned actor is active or its closure is unconfirmed.')
 owner=c.get('owner',{})
 if all(k in owner for k in ['pid','startticks']) and actor_alive(owner):raise ValueError('The owned controller is still active.')
 if r.get('released') is not True or not c.get('claim_key') or r.get('claim_key')!=c['claim_key']:
  raise ValueError('The owned claim is not released.')
 identity=c.get('batch_identity')
 if identity:
  aggregate=Path(identity['aggregate_path'])
  if not str(aggregate).startswith('/sys/fs/cgroup/') or aggregate.parent.name!='zesuworkloads.slice' or not re.fullmatch(r'zesuworkloads-aggregate[0-9]+p[0-9]+r[0-9]+\.slice',aggregate.name):
   raise ValueError('The closed aggregate identity is unsupported.')
  if aggregate.exists():
   current=aggregate.stat()
   if current.st_dev!=identity['aggregate_device'] or current.st_ino!=identity['aggregate_inode']:
    raise ValueError('The aggregate identity changed before cleanup.')
   events=dict(line.split() for line in (aggregate/'cgroup.events').read_text().splitlines())
   if events.get('populated')!='0':raise ValueError('The owned aggregate still has actors.')
 if job['phase']=='native':
  dispatch=directory/'DISPATCH-FINISHED.json'
  if not dispatch.is_file() or load(dispatch).get('result')!=binding(result):
   raise ValueError('Native result processing is not sealed.')
 return {'result':binding(result),'closure':binding(closure),'release':binding(release)}


def finish(config,out):
 out=Path(out).absolute();receipt=out/'END-CLEANUP.json'
 if receipt.exists():return load(receipt)
 setting=config.get('end_of_run_cleanup',policy())
 if set(setting)!={'schema','enabled'} or setting['schema']!='scratch.end-run-cleanup.v1' or type(setting['enabled']) is not bool:
  raise ValueError('The cleanup policy is malformed.')
 report={'schema':'scratch.end-run-cleanup.result.v1','enabled':setting['enabled'],'run_root':str(out),'removed':[],
         'allocated_bytes_unlinked':0,'physical_recovery_bytes':None,'accounting':'Allocated file bytes unlinked. Shared extents and final-link recovery are unmeasured.'}
 if not setting['enabled']:
  report.update(status='disabled',reason='The caller retained reusable files.');write_once(receipt,report);return report
 try:
  contained(out,out)
  if not (out/'RESULT.json').is_file():raise ValueError('The outer result is not sealed.')
  lifecycle=[row for job in config['jobs'] if (row:=closed_job(job,out)) is not None]
  if not lifecycle:raise ValueError('No closed owned job exists.')
  roots=[];prepared=Path(config['prepared_workspace'])
  if prepared==out/'prepared':roots.append(contained(out,prepared))
  else:report['external_prepared_workspace_retained']=str(prepared)
  for job in config['jobs']:
   workspace=out/'jobs'/job['key']/'workspace'
   if workspace.exists() or workspace.is_symlink():roots.append(contained(out,workspace))
  candidates=[]
  for root in roots:
   for parent,dirs,files in os.walk(root,followlinks=False):
    dirs[:]=[name for name in dirs if not (Path(parent)/name).is_symlink()]
    for name in files:
     path=Path(parent)/name;info=path.lstat()
     if stat.S_ISREG(info.st_mode) and info.st_size>=MINIMUM_BYTES and path.suffix in ARTIFACT_SUFFIXES:
      contained(out,path);candidates.append((path,info))
  seal={'schema':'scratch.end-result-seal.v1','result':binding(out/'RESULT.json'),'lifecycle':lifecycle,'time_ns':time.time_ns()}
  seal_path=out/'END-RESULT-SEALED.json'
  if seal_path.exists():
   prior=load(seal_path)
   if prior['result']!=seal['result'] or prior['lifecycle']!=seal['lifecycle']:raise ValueError('The sealed result changed before cleanup.')
  else:write_once(seal_path,seal)
  report['seal']=binding(seal_path)
  for path,prior in candidates:
   current=path.lstat()
   if (current.st_dev,current.st_ino,current.st_size,current.st_mtime_ns)!=(prior.st_dev,prior.st_ino,prior.st_size,prior.st_mtime_ns):
    raise ValueError('A copied artifact changed before cleanup.')
   path.unlink();allocated=prior.st_blocks*512
   report['removed'].append({'path':str(path.relative_to(out)),'size_bytes':prior.st_size,'allocated_bytes':allocated,'links_before':prior.st_nlink})
   report['allocated_bytes_unlinked']+=allocated
  report['status']='cleaned';report['removed_count']=len(report['removed'])
 except (ValueError,OSError,KeyError) as error:
  report.update(status='refused',reason=str(error))
 write_once(receipt,report);return report
