"""Validate a completed common prefix and one reviewed arm delta."""
from pathlib import Path
import hashlib,json

def bound(row):
 path=Path(row['path'])
 if hashlib.sha256(path.read_bytes()).hexdigest()!=row['sha256']:raise ValueError('A minimal-prefix input changed.')
 return path

def read(row):return json.loads(bound(row).read_text())

def closed(closure_binding,release_binding):
 closure=read(closure_binding);release=read(release_binding)
 if (closure.get('all_owned_actors_closed') is not True or any(r.get('ended') is not True for r in closure.get('actors',[]))
     or release.get('released') is not True or closure.get('claim_key')!=release.get('claim_key')):
  raise ValueError('The minimal prefix has not closed and released.')
 return release

def declaration_fence(prefix):
 if prefix['fence_bytes']==24*1024**3:return
 if prefix['fence_bytes']!=64*1024**3:raise ValueError('The common prefix has an unsupported declaration fence.')
 evidence=prefix.get('fence_evidence') or {}
 if set(evidence)!={'runtime','result','client_limits','batch'}:raise ValueError('The 64 GiB prefix lacks physical fence evidence.')
 ready=read(prefix['ready_runtime']);job=ready['jobs'][0];out=Path(job['output'])
 from memory_policy import validate_job
 if job.get('phase')!='prerequisites' or validate_job(job)!=24*1024**3 or job.get('physical_fence_bytes')!=64*1024**3:
  raise ValueError('The completed declaration job has another memory policy.')
 for key,name in [('runtime','RUNTIME.json'),('result','RESULT.json'),('client_limits','CLIENT-LIMITS.json'),('batch','BATCH-IDENTITY.json')]:
  if Path(evidence[key]['path'])!=out/name:raise ValueError('The physical fence evidence leaves its exact job.')
 runtime,limits,batch=(read(evidence[k]) for k in ['runtime','client_limits','batch'])
 if (runtime.get('phase')!='prerequisites' or runtime.get('job_output')!=str(out) or
     runtime.get('ordered_modules')!=job.get('ordered_modules') or
     runtime.get('canonical_admission',{}).get('memory_job')!=job):
  raise ValueError('The completed inner runtime differs from the READY job.')
 if (limits.get('effective_limits')!={'memory.max':64*1024**3,'memory.swap.max':0} or
     limits.get('pid')!=batch.get('inside_pid') or str(limits.get('startticks'))!=str(batch.get('inside_startticks'))):
  raise ValueError('The physical client receipt does not prove a 64 GiB fence.')
 closure=read(prefix['closure'])
 if (Path(prefix['closure']['path'])!=out/'CLOSURE.json' or Path(prefix['release']['path'])!=out/'RELEASE.json' or
     closure.get('batch_identity')!=batch or read(evidence['result']).get('success') is not True):
  raise ValueError('The completed declaration result or lifecycle names another aggregate.')

def common(binding):
 prefix=read(binding)
 if prefix.get('status')!='passed' or prefix.get('native_calls')!=0:
  raise ValueError('The common prefix did not complete as declarations.')
 bound(prefix['ready_runtime']);release=closed(prefix['closure'],prefix['release'])
 if prefix['claim_bytes']!=24*1024**3 or release.get('bytes')!=prefix['claim_bytes']:
  raise ValueError('The common prefix has another declaration fence or release.')
 declaration_fence(prefix)
 names=[]
 for row in prefix['modules']:
  names.append(row['module']);bound(row['source']);bound(row['object']);receipt=read(row['receipt'])
  if (receipt.get('result',{}).get('success') is not True or receipt['source_sha256']!=row['source']['sha256']
      or receipt['object_sha256']!=row['object']['sha256']):
   raise ValueError('A common source/object pair differs from its compile receipt.')
  bound({'path':receipt['source'],'sha256':receipt['source_sha256']});bound({'path':receipt['object'],'sha256':receipt['object_sha256']})
 if len(names)!=len(set(names)):raise ValueError('A common prefix module repeats.')
 return prefix

def validate(packet,workspace,modules,*,complete_delta=False,evidence=None):
 prefix=common(packet['common_prefix']);base={r['module']:r for r in prefix['modules']}
 if list(base)!=packet['ordered_modules']:raise ValueError('The authority differs from the completed common order.')
 sources={r['module']:r for r in packet['source_inventory']};delta=packet['prerequisite_delta']
 if delta not in ([],['ZesuSsz.Evidence.RuleScratchRules']):
  raise ValueError('An earlier common-module change requires a new common prefix.')
 changed=[name for name in base if sources[name]['sha256']!=base[name]['source']['sha256']]
 if delta!=changed:raise ValueError('The arm delta differs from its exact source changes.')
 staged=Path(workspace)
 for name,row in base.items():
  if name in delta:continue
  obj=(staged/modules[name]).with_suffix('.vo')
  if not obj.is_file() or hashlib.sha256(obj.read_bytes()).hexdigest()!=row['object']['sha256']:
   raise ValueError('A reused common object differs from its compiled prefix.')
 if not complete_delta:return
 if not delta:
  if evidence:raise ValueError('An unchanged arm has an unexpected delta receipt.')
  return
 if not evidence:raise ValueError('The native arm lacks its completed delta receipts.')
 result=read(evidence['result']);closed(evidence['closure'],evidence['release'])
 if result.get('success') is not True:raise ValueError('The arm delta did not compile successfully.')
 if [r['module'] for r in evidence['receipts']]!=delta:raise ValueError('The delta receipt order differs from its authority.')
 for row in evidence['receipts']:
  name=row['module'];receipt=read(row['receipt']);obj=(staged/modules[name]).with_suffix('.vo')
  if (receipt.get('result',{}).get('success') is not True or receipt['source_sha256']!=sources[name]['sha256']
      or not obj.is_file() or hashlib.sha256(obj.read_bytes()).hexdigest()!=receipt['object_sha256']):
   raise ValueError('A staged delta object differs from its successful source receipt.')

def delta_evidence(config,route):
 packet=read(route);delta=packet['prerequisite_delta']
 if not delta:return None
 job=Path(config['jobs'][0]['output'])
 def binding(path):return {'path':str(path),'sha256':hashlib.sha256(path.read_bytes()).hexdigest()}
 return {'result':binding(job/'RESULT.json'),'closure':binding(job/'CLOSURE.json'),'release':binding(job/'RELEASE.json'),
         'receipts':[{'module':name,'receipt':binding(job/'native'/('dependency-'+name+'.json'))} for name in delta]}

def bindings(packet):
 prefix=common(packet['common_prefix']);rows=[packet['common_prefix'],prefix['ready_runtime'],prefix['closure'],prefix['release']]
 rows += list(prefix.get('fence_evidence',{}).values())
 for module in prefix['modules']:rows += [module[key] for key in ['source','object','receipt']]
 return rows
