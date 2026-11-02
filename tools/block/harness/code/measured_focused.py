"""Validate the explicit completed-error control booking without proof acceptance."""
from pathlib import Path
import hashlib,json
POLICY=Path(__file__).resolve().parents[1]/'policies/FOCUSED-CONTROL-PEAK.json'
POLICY_SHA='79927c5760cb0d38cd33779a4a51d3daa4d8ffa70788313cf66cdbd1a5fdcf8b'
BOOKING='completed_control_peak'
def read(ref):
 p=Path(ref['path'])
 if hashlib.sha256(p.read_bytes()).hexdigest()!=ref['sha256']:raise ValueError('A completed control binding changed.')
 return json.loads(p.read_text())
def authority(profile):
 ref=profile.get('completed_control_peak')
 if not isinstance(ref,dict) or ref.get('sha256')!=POLICY_SHA:raise ValueError('The completed control authority is not approved.')
 value=read(ref)
 if value.get('schema')!='scratch.completed-control-peak-authority.v1':raise ValueError('The completed control schema differs.')
 return value

def references(profile):
 a=authority(profile);m=read(a['measurement'])
 return [profile['completed_control_peak'],a['measurement'],a['prior_runtime'],a['prior_job_runtime'],*[m[k] for k in ['completed_failed_run','accounting','calls','closure','release','subject','session','profile_origin']]]

def claim(profile,config,ordered=()):
 a=authority(profile);m=read(a['measurement']);prior=read(a['prior_runtime']);inner=read(a['prior_job_runtime'])
 if list(ordered)!=inner.get('ordered_modules',[]) or profile.get('sources')!=read(m['profile_origin']).get('sources'):raise ValueError('The measured control compile boundary differs.')
 if (config.get('control_session')!=a['current_control_session'] or read(m['session'])!=a['current_control_session'] or prior.get('control_session')!=a['prior_control_session'] or inner.get('control_session')!=a['prior_control_session']):raise ValueError('The completed control comparison transition differs.')
 if config.get('effective_compiler_version',{}).get('compiler')!=inner.get('physical_compiler'):raise ValueError('The completed control compiler differs.')
 row=profile.get('control_source',{});module=a['source_module'];workspace=Path(config['prepared_workspace'])
 if row.get('role')!='consumer_check' or row.get('module')!=module or row.get('sha256')!=a['source_sha256'] or m['subject']['sha256']!=a['source_sha256']:raise ValueError('The completed control source boundary differs.')
 source=workspace/config['proof_runtime']['module_files'][module]
 if hashlib.sha256(source.read_bytes()).hexdigest()!=a['source_sha256']:raise ValueError('The actual completed control source differs.')
 old=Path(prior['prepared_workspace'])/prior['proof_runtime']['module_files'][module]
 if not any(x['path']==str(old) and x['sha256']==a['source_sha256'] for x in prior['bindings']):raise ValueError('The historical control source is not bound.')
 def normal(flags,root):return [x.replace(str(root),'{workspace}') for x in flags]
 if normal(config.get('physical_flags',[]),workspace)!=normal(prior['physical_flags'],prior['prepared_workspace']):raise ValueError('The completed control compiler flags differ.')
 directory=Path(inner['job_output']);result=read(m['completed_failed_run']);cpu=read(m['accounting']);closure=read(m['closure']);release=read(m['release']);read(m['calls']);read(m['profile_origin'])
 for key,name in [('completed_failed_run','RESULT.json'),('accounting','CPU-FINAL.json'),('closure','CLOSURE.json'),('release','RELEASE.json')]:
  if Path(m[key]['path'])!=directory/name:raise ValueError('The completed control evidence leaves its job.')
 if (inner['phase']!='prerequisites' or result.get('phase')!='prerequisites' or result.get('status')!='infrastructure_failed' or result.get('returncode')!=1 or result.get('resource_reason') or result.get('CPU')!=cpu or result.get('aggregate_peak_bytes')!=cpu.get('aggregate_peak_bytes')):raise ValueError('The approved completed-error result differs.')
 if cpu.get('CPU_budget_enforced') is not False or cpu.get('final_memory_accounting_available') is not True or not cpu.get('memory_events',{}).get('available'):raise ValueError('The completed control accounting is incomplete or capped.')
 if any(cpu['memory_events']['counters'].get(k,0)>0 for k in ['max','oom','oom_kill','oom_group_kill']):raise ValueError('The completed control hit a memory limit.')
 if (closure.get('all_owned_actors_closed') is not True or not closure.get('actors') or any(x.get('ended') is not True for x in closure['actors']) or release.get('released') is not True or release.get('claim_key')!=closure.get('claim_key') or release.get('bytes',0)<=0):raise ValueError('The completed control lifecycle is incomplete.')
 peak=cpu.get('aggregate_peak_bytes')
 if type(peak) is not int or peak<=0 or peak!=m['peak_bytes']:raise ValueError('The completed control peak differs.')
 value=max(8*1024**3,(3*peak+1)//2)
 if value!=m['claim_bytes'] or value>64*1024**3 or m['physical_fence_bytes']!=64*1024**3:raise ValueError('The completed control claim or fence differs.')
 return value
