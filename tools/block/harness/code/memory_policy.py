"""Select phase fences and claims from completed, source-bound stock returns."""
from pathlib import Path
import hashlib,json,re
GIB=1024**3
NATIVE_FENCE=64*GIB
COMPILE_FENCE=24*GIB
PARENT_FENCE=175*GIB
QUANTUM=8*GIB
COMPILE_PHASES={'prerequisites','kernel','compile_only'}

def bound(row):
 path=Path(row['path'])
 if hashlib.sha256(path.read_bytes()).hexdigest()!=row['sha256']:raise ValueError('A memory evidence binding changed: '+str(path))
 return path

def read(row):return json.loads(bound(row).read_text())

def fence(phase):
 if phase in COMPILE_PHASES:return NATIVE_FENCE
 if phase=='native':return NATIVE_FENCE
 raise ValueError('The memory phase is unsupported: '+str(phase))

def rounded_claim(peak):
 if type(peak) is not int or peak<=0:raise ValueError('A completed peak must be a positive integer.')
 return ((3*peak+2*QUANTUM-1)//(2*QUANTUM))*QUANTUM

def groups(state):
 for name in ['goals','stack','shelf','given_up']:
  if not isinstance(state.get(name),list):raise ValueError('A completed state omits a group.')
 frames=state['stack']
 if any(not isinstance(x,list) or len(x)!=2 or any(not isinstance(y,list) for y in x) for x in frames):raise ValueError('A completed focus frame is invalid.')
 return {'active':len(state['goals']),'focus_frames':len(frames),'frame_goals':sum(len(a)+len(b) for a,b in frames),'shelves':len(state['shelf']),'given_up':len(state['given_up'])}

def rounded_rss_claim(peak):
 if type(peak) is not int or peak<=0:raise ValueError('A completed RSS peak must be positive.')
 return max(QUANTUM,((3*peak+8*GIB+2*QUANTUM-1)//(2*QUANTUM))*QUANTUM)

def legacy_statement_matches(row,target,source):
 if row.get('statement_sha256')==target.get('statement_sha256'):return True
 if not row.get('declaration_projection'):return False
 projection=read(row['declaration_projection'])
 if projection.get('schema')!='legacy-stock.declaration-projection.v1' or projection.get('native_source')!=row['native_source']:return False
 current=bound(projection['current_source'])
 if projection['current_source']['sha256']!=target.get('source_sha256') or current.read_bytes()!=source.read_bytes():return False
 from scratch_statement import source_statement
 spec=source_statement(source);actual=source_statement(current)
 if projection.get('theorem')!=spec['name'] or actual['name']!=spec['name']:return False
 interval=spec['statement']+spec['pre_proof_commands']
 if interval!=bound(projection['legacy_interval']).read_text() or hashlib.sha256(interval.encode()).hexdigest()!=row['statement_sha256']:return False
 declaration=bound(projection['declaration']).read_text()
 return declaration==spec['statement']==actual['statement'] and hashlib.sha256(declaration.encode()).hexdigest()==target.get('statement_sha256')

def completed_legacy(row,target):
 if row.get('route')!='stock_zesu_block':return None,'The legacy measurement does not use stock search.'
 if row.get('module')!=target.get('module'):return None,'The legacy module boundary differs.'
 source=bound(row['native_source']);text=source.read_text()
 if row['native_source']['sha256']!=target.get('source_sha256'):return None,'The legacy native source differs.'
 if not legacy_statement_matches(row,target,source):return None,'The legacy declaration projection differs.'
 if 'Ltac ' in text or 'RuleScratchRules' in text or 'checkpoint_' in text or not re.search(r'Proof\.\s*zesu_block\.\s*Qed\.',text):return None,'The legacy caller is not plain stock.'
 result,acceptance=read(row['result']),read(row['acceptance'])
 if result.get('source_sha256')!=target['source_sha256'] or result.get('statement_sha256')!=row['statement_sha256']:return None,'The legacy result names another boundary.'
 if '.'.join(Path(result['source']).with_suffix('').parts)!=target['module']:return None,'The legacy module differs.'
 if result.get('module_m') is not True or result.get('assumptions')!=[] or result.get('native_invocations')!=1 or result.get('normal_transports') is not True:return None,'The stock compile did not finish successfully.'
 if (result.get('telemetry_errors') or {}).get('count')!=0 or result.get('inputs_unchanged') is False:return None,'The legacy measurement has invalid input or telemetry evidence.'
 if acceptance.get('accepted') is not True or acceptance.get('result_sha256')!=row['result']['sha256'] or acceptance.get('all_recorded_actors_ended') is not True:return None,'The legacy acceptance is absent or mismatched.'
 if not result.get('actor_closure') or any(x.get('ended') is not True for x in result['actor_closure']):return None,'A legacy actor remains open.'
 peak_kib=result.get('peak_rss_kib')
 if type(peak_kib) is not int or peak_kib<=0:return None,'The completed RSS is unavailable.'
 compiler=read(row['compiler'])
 if result.get('raw_hashes',{}).get(row['compiler']['path'])!=row['compiler']['sha256']:return None,'The compiler receipt is not result-bound.'
 if compiler.get('exit_code')!=0 or compiler.get('measurement_complete') is not True or compiler.get('limit') is not None or compiler.get('policy_error') is not None:return None,'The physical compile is partial or capped.'
 if compiler.get('peak_rss_kib')!=peak_kib or (compiler.get('telemetry_errors') or {}).get('count')!=0:return None,'The RSS scope or telemetry differs.'
 if not compiler.get('command') or Path(compiler['command'][-1]).resolve()!=source.resolve():return None,'The measured command names another source.'
 before=compiler.get('scope_memory_events_before') or {};after=compiler.get('scope_memory_events_after') or {}
 if any(after.get(key,0)>before.get(key,0) for key in ['oom','oom_kill','oom_group_kill']):return None,'The physical compile records an OOM.'
 ledger=read(row['release_ledger']);key=row['claim_key'];released=ledger.get('fixed_claim_releases',{}).get(key)
 if ledger.get('fixed_claims',{}).get(key)!=0 or released!=row['claim_release'] or not released:return None,'The legacy claim is not released.'
 if released.get('review_sha256')!=row['acceptance']['sha256'] or released.get('all_recorded_actors_ended') is not True:return None,'The release names another review.'
 peak=peak_kib*1024
 return {'measurement':row,'peak_bytes':peak,'scope':'Completed legacy R1 physical-workload peak RSS; not aggregate memory.peak.','memory_metric':'workload_RSS','client_server_allowance_bytes':4*GIB,'formula':'ceil_to_8GiB(max(8GiB, 1.5 * completed_RSS_bytes + 4GiB))','claim_bytes':rounded_rss_claim(peak),'qualification':row.get('qualification')},None

def completed_verified_repair(row,target):
 if row.get('route')!='stock_zesu_block':return None,'The repaired measurement does not use stock search.'
 from verification_supplement import validate
 supplement=read(row['verification_supplement']);full=supplement['target']
 if any(full.get(k)!=target.get(k) for k in ['module','source_sha256','statement_sha256']):return None,'The repaired source boundary differs.'
 if row['native_source']!=supplement['source'] or row['result']!=supplement['original_result']:return None,'The repaired row names another source or result.'
 checked=validate(row['verification_supplement'],full,row['result'])
 peak=checked['native_peak_bytes']
 return {'measurement':row,'peak_bytes':peak,'scope':checked['scope'],'claim_bytes':rounded_claim(peak),'formula':'ceil_to_8GiB(1.5 * completed_aggregate_peak_bytes)','memory_metric':'aggregate_memory.peak','client_server_allowance_bytes':0,'qualification':row.get('qualification'),'verification_repair':checked},None

def completed(row,target):
 if row.get('format')=='completed_stock_verification_repair_v1':return completed_verified_repair(row,target)
 if row.get('format')=='legacy_r1_workload_rss_v1':return completed_legacy(row,target)
 if row.get('route')!='stock_zesu_block':return None,'The measurement does not use the stock route.'
 if any(row.get(key)!=target.get(key) for key in ['module','statement_sha256']):return None,'The module or statement differs.'
 source=bound(row['native_source']);text=source.read_text()
 if row['native_source']['sha256']!=target.get('source_sha256'):return None,'The native source differs.'
 if 'Ltac ' in text or 'RuleScratchRules' in text or 'checkpoint_' in text or not re.search(r'Proof\.\s*zesu_block\.\s*Qed\.',text):return None,'The source contains a private or nonstock caller.'
 result=read(row['result'])
 if result.get('module')!=target['module'] or result.get('statement_sha256')!=target['statement_sha256']:return None,'The result names another source boundary.'
 if result.get('status') not in {'passed','native_open'} or result.get('normal_tactic_return') is not True:return None,'The native tactic did not return normally.'
 if result.get('resource_reason') or result.get('shared_infrastructure_failure'):return None,'The measurement stopped or failed.'
 cpu=result.get('CPU') or {}
 if result.get('final_memory_accounting_available') is not True or cpu.get('final_memory_accounting_available') is not True:return None,'Final memory accounting is unavailable.'
 events=(cpu.get('memory_events') or {}).get('counters') or {}
 if any(events.get(key,0)>0 for key in ['oom','oom_kill','oom_group_kill']):return None,'The aggregate records an OOM event.'
 state_binding=result.get('complete_state')
 if not state_binding or state_binding.get('state_source')!='successful_command_returned_state':return None,'The interrupted or partial state is ineligible.'
 state=read(state_binding)
 try:
  actual=groups(state);kernel=groups(state.get('kernel_groups',{}))
 except ValueError:return None,'The complete groups are unavailable.'
 if actual!=result.get('group_counts') or kernel!=actual:return None,'The complete groups do not match.'
 peak=result.get('aggregate_peak_bytes')
 if type(peak) is not int or peak<=0 or cpu.get('aggregate_peak_bytes')!=peak:return None,'The completed peak is missing or inconsistent.'
 closure,release=read(row['closure']),read(row['release'])
 if closure.get('all_owned_actors_closed') is not True or release.get('released') is not True or not (release.get('bytes',release.get('released_bytes',0))>0):return None,'Closure or claim release is incomplete.'
 if not cpu.get('scope'):return None,'The memory scope is unavailable.'
 return {'measurement':row,'peak_bytes':peak,'scope':cpu['scope'],'claim_bytes':rounded_claim(peak),'formula':'ceil_to_8GiB(1.5 * completed_aggregate_peak_bytes)','memory_metric':'aggregate_memory.peak','client_server_allowance_bytes':0,'qualification':row.get('qualification')},None

def select(rows,target):
 accepted=[];refused=[]
 for row in rows:
  if row.get('module')!=target.get('module'):continue
  value,reason=completed(row,target)
  if value:accepted.append(value)
  else:refused.append({'result':row.get('result'),'reason':reason})
 selected=max(accepted,key=lambda x:(x['claim_bytes'],x['peak_bytes'])) if accepted else None
 return selected,refused


FAMILY_KIND='stock_pass_spec_bundle'
FOCUSED_KIND='focused_check'
FAMILY_DEFAULT_CLAIM=16*GIB
MINIMAL_NATIVE_CLAIM=8*GIB
FOCUSED_CLAIM=8*GIB
PORT_KIND='production_stock_port'
PORT_FENCE=32*GIB
PORT_AUTHORITY={'path': str(Path(__file__).resolve().parents[1]/'policies'/'PORT-FAMILY-AUTHORITY-22.json'), 'sha256': 'ea88c0e9eab9e6e720e7fc2500407c065d82fd7a0feb12658783d4a761c79917'}
PORT_EXTENSION={'path': str(Path(__file__).resolve().parents[1]/'policies'/'EXTENSION.json'), 'sha256': 'ad05524ccec944621e775ebaccf5cd39b766bd6d4c554bbfa7f8332d84d77913'}

def relocated_authority(actual,expected,legacy_paths=()):
 """Permit only approved byte-identical authority relocation."""
 if (not isinstance(actual,dict) or set(actual)!={'path','sha256'} or
     actual['sha256']!=expected['sha256']):return False
 roots=[Path(expected['path']).parent]+[Path(name).parent for name in legacy_paths]
 path=Path(actual['path']).resolve()
 if not any(path.is_relative_to(root.resolve()) for root in roots):
  raise ValueError('An authority relocation leaves its approved roots.')
 before=bound(expected).read_bytes();after=bound(actual).read_bytes()
 if before!=after:raise ValueError('An authority relocation changes the approved bytes.')
 return True

def production_port_authority(profile):
 if set(profile) not in ({'schema','kind','authority','memory_route'},{'schema','kind','authority','memory_route','supplier_ready'}) or profile.get('schema')!='scratch.admission-profile.v1' or profile.get('kind')!=PORT_KIND or profile.get('memory_route')!='measured_native':
  raise ValueError('The production PORT profile is invalid.')
 if not relocated_authority(profile['authority'],PORT_AUTHORITY,('/home/cody/zesislar/_build/agents/worker-build-2/PORT-union-v2/matrix005-authority-v1/PORT-FAMILY-AUTHORITY-22.json', '/home/cody/zesislar/_build/agents/worker-build-2/PORT-matrix006-authority-v1/PORT-FAMILY-AUTHORITY-22.json')):raise ValueError('The production PORT authority is not authorized.')
 authority=read(profile['authority'])
 if (authority.get('schema')!='port.production-stock-family-authority.v1' or
     authority.get('claim_bytes')!=8*GIB or authority.get('physical_fence_bytes')!=PORT_FENCE or
     authority.get('native_body')!='zesu_block.' or authority.get('setup_order')!=[] or
     authority.get('minimal_or_private_route') is not False or authority.get('fence_hit_retry') is not False):
  raise ValueError('The production PORT ruling differs.')
 cases=authority['cases']
 extension=read(PORT_EXTENSION)
 read(extension['exit_queue'])
 if (extension.get('case_count')!=22 or not relocated_authority(authority.get('authority_extension'),PORT_EXTENSION,('/home/cody/zesislar/_build/agents/worker-build-2/native-port-policy-v1/source014-authority22-caller002-extension/EXTENSION.json', '/home/cody/zesislar/_build/agents/worker-build-2/PORT-matrix006-authority-v1/EXTENSION.json'))
     or cases!=extension['original_cases']+extension['additional_cases']
     or len(cases)!=22 or len({r['block'] for r in cases})!=22 or len({r['module'] for r in cases})!=22):
  raise ValueError('The production PORT case set differs from the exact released22 inventory.')
 if 'supplier_ready' in profile:
  from supplier_ready import validate,ROOTS
  supplier=validate(profile['supplier_ready'])
  authority=dict(authority,production_sources=[dict(row['source'],module=row['module']) for row in supplier['modules'] if row['module'] in ROOTS])
 for row in authority['production_sources']:bound(row)
 if {r['module'] for r in authority['production_sources']}!={'ZesuSsz.Automation.All','ZesuSsz.Automation.Hooks','ZesuSsz.Automation.Finish'}:
  raise ValueError('The production PORT owners differ.')
 return authority

def production_port_case(profile,job):
 authority=production_port_authority(profile)
 if job['phase']!='native' or job.get('native_route') is not None or job.get('ordered_modules',[])!=[]:
  raise ValueError('The production PORT job requires stock native search with empty setup.')
 target=job['target'];rows=[r for r in authority['cases'] if r['block']==job['key'] and r['module']==target['module']]
 if len(rows)!=1:raise ValueError('The production PORT case is not authorized.')
 case=rows[0]
 if target.get('pc')!=case['pc']:raise ValueError('The production PORT address differs.')
 if target.get('source_sha256')!=case['source']['sha256'] or target.get('statement_sha256')!=case['statement_sha256']:
  raise ValueError('The production PORT source or statement differs.')
 return authority,case

def workload_for_job(profile_binding,job,config):
 if not profile_binding:return None
 profile=read(profile_binding)
 if profile.get('schema')!='scratch.admission-profile.v1':raise ValueError('The admission profile is unsupported.')
 kind=profile.get('kind')
 if kind not in {FAMILY_KIND,FOCUSED_KIND,'minimal_native_tactic',PORT_KIND}:raise ValueError('The workload kind is unsupported.')
 if kind in {FAMILY_KIND,'minimal_native_tactic',PORT_KIND} and job['phase']!='native' or kind==FOCUSED_KIND and job['phase']=='native':return None
 modules=config['proof_runtime']['module_files'];workspace=Path(config['prepared_workspace']);owned=[]
 def actual(row):
  source=bound(row)
  if row['module'] not in modules:raise ValueError('The workload source module is absent.')
  staged=workspace/modules[row['module']]
  if hashlib.sha256(staged.read_bytes()).hexdigest()!=row['sha256']:raise ValueError('The actual workload source differs.')
  owned.append({'module':row['module'],'path':str(staged),'sha256':row['sha256']})
  return source
 if kind=='minimal_native_tactic':
  from native_route import validate
  packet=validate(profile['authority'],workspace=workspace,modules=modules,target=job['target'],ordered=job.get('ordered_modules',[]))
  for row in packet['source_inventory']:actual(row)
  return {'kind':kind,'profile':profile_binding,'owned_sources':owned,'declarations_only':False,'native_route':profile['authority']}
 if kind==PORT_KIND:
  authority,case=production_port_case(profile,job)
  if config.get('native_route') is not None or config.get('declarations_only') or config.get('prerequisite_modules')!=[]:
   raise ValueError('The production PORT runtime requires stock native search with empty setup.')
  source=actual(dict(case['source'],module=case['module']));text=source.read_text()
  if not text.startswith('Require Import ZesuSsz.Automation.All.\n') or re.search(r'\b(?:Ltac2?|RuleScratchRules|AllLegacy)\b',text):
   raise ValueError('The production PORT caller is not plain production stock.')
  from scratch_statement import source_statement
  specification=source_statement(source,'zesu_block.')
  if hashlib.sha256(specification['statement'].encode()).hexdigest()!=case['statement_sha256']:
   raise ValueError('The production PORT declaration differs.')
  for row in authority['production_sources']:actual(row)
  result={'kind':kind,'profile':profile_binding,'owned_sources':owned,'declarations_only':False,'prerequisite_modules':[]}
  if 'supplier_ready' in profile:
   from supplier_ready import validate,staged
   sources=staged(validate(profile['supplier_ready']),config)
   known={row['module'] for row in owned}
   owned.extend(row for row in sources if row['module'] not in known)
   result['supplier_context']={key:config[key] for key in ['expected_mcp_flags','physical_flags','effective_compiler_version','cache_import_graph']}
   result['supplier_context']['supplier_flag_workspace']=str(config.get('supplier_flag_workspace',config['prepared_workspace']))
  return result
 if kind==FOCUSED_KIND:
  if not config.get('declarations_only'):raise ValueError('A focused check must use declaration-only execution.')
  rows=profile['sources']
  if set(job.get('ordered_modules',[]))!={r['module'] for r in rows}:raise ValueError('The focused source list must cover every compiled module.')
  if len(rows)!=len({r['module'] for r in rows}):raise ValueError('A focused module repeats.')
  for row in rows:
   if row.get('role') not in {'generated_declarations','consumer_check'}:raise ValueError('A rule compilation retains its full claim.')
   if re.search(r'\bzesu_block\b',actual(row).read_text()):raise ValueError('A focused check contains a native proof.')
 else:
  native=profile['native_source'];source=actual(native);text=source.read_text()
  if native['module']!=job['target']['module'] or native['sha256']!=job['target']['source_sha256']:raise ValueError('The family native source differs.')
  if 'Ltac ' in text or 'checkpoint_' in text or not re.search(r'Proof\.\s*zesu_block\.\s*Qed\.',text):raise ValueError('The family requires the plain stock caller.')
  if profile['pass_entries']['module']!='ZesuSsz.Generated.DecodeItem.Entries':raise ValueError('The family requires the pass entry module.')
  actual(profile['pass_entries']);actual(profile['bundle_source']);bound(profile['spec_recipe'])
 return {'kind':kind,'profile':profile_binding,'owned_sources':owned,'declarations_only':bool(config.get('declarations_only'))}

def minimal_growth_claim(profile,target):
 evidence=profile.get('observed_growth')
 if evidence is None:return MINIMAL_NATIVE_CLAIM
 if set(evidence)!={'runtime','accounting','aggregate'}:raise ValueError('The minimal growth evidence is incomplete.')
 runtime=read(evidence['runtime']);prior=runtime.get('target',{}).get('block') or {}
 if runtime.get('phase')!='native' or any(prior.get(k)!=target.get(k) for k in ['module','source_sha256','statement_sha256']):raise ValueError('The growth observation names another block or source.')
 directory=Path(runtime['job_output']);accounting_path=bound(evidence['accounting']);aggregate_path=bound(evidence['aggregate'])
 if aggregate_path!=directory/'BATCH-IDENTITY.json' or accounting_path.parent!=directory or accounting_path.name not in {'CPU-FINAL.json','MEMORY-CLAIM-REPORT.json'}:raise ValueError('The growth observation leaves its exact job.')
 accounting=read(evidence['accounting']);aggregate=read(evidence['aggregate'])
 if accounting_path.name=='CPU-FINAL.json':
  if accounting.get('final_memory_accounting_available') is not True or accounting.get('memory_peak_source')!=aggregate['aggregate_path']+'/memory.peak':raise ValueError('The final growth accounting lacks its aggregate identity.')
  peak=accounting.get('aggregate_peak_bytes')
 else:
  actual=accounting.get('aggregate',{})
  if accounting.get('report_only') is not True or any(actual.get(k)!=aggregate.get(k) for k in ['aggregate_path','aggregate_device','aggregate_inode']):raise ValueError('The live growth report names another aggregate.')
  peak=accounting.get('memory_peak_bytes')
 if type(peak) is not int or peak<=0:raise ValueError('The growth observation lacks a positive measured peak.')
 return max(MINIMAL_NATIVE_CLAIM,(3*peak+1)//2) if peak>MINIMAL_NATIVE_CLAIM else MINIMAL_NATIVE_CLAIM


def workload_claim(workload,job,basis):
 if not workload:return basis['claim_bytes'] if basis else (COMPILE_FENCE if job['phase'] in COMPILE_PHASES else fence(job['phase']))
 owned=workload['owned_sources']
 for row in owned:bound(row)
 context={'proof_runtime':{'module_files':{r['module']:r['path'] for r in owned}},'prepared_workspace':'/','declarations_only':workload['declarations_only'],'prerequisite_modules':workload.get('prerequisite_modules')}
 if 'supplier_context' in workload:
  if (workload['kind']!=PORT_KIND or set(workload['supplier_context'])!={'expected_mcp_flags','physical_flags','effective_compiler_version','cache_import_graph','supplier_flag_workspace'}):
   raise ValueError('The supplier workload context is invalid.')
  context.update(workload['supplier_context'])
 actual=workload_for_job(workload['profile'],job,context)
 if actual is None or actual['kind']!=workload['kind']:raise ValueError('The workload evidence is invalid.')
 kind=read(workload['profile']).get('kind')
 if kind!=workload['kind']:raise ValueError('The workload profile kind changed.')
 if kind=='minimal_native_tactic':
  if job['phase']!='native' or job.get('native_route')!=actual['native_route']:
   raise ValueError('The minimal native job lost its reviewed authority.')
  return minimal_growth_claim(read(workload['profile']),job['target'])
 if kind==FOCUSED_KIND:
  if job['phase'] not in COMPILE_PHASES:raise ValueError('A focused check cannot execute native search.')
  return FOCUSED_CLAIM
 if kind==PORT_KIND:return 8*GIB
 if kind==FAMILY_KIND:
  if job['phase']!='native':raise ValueError('The stock family requires a native phase.')
  return basis['claim_bytes'] if basis else FAMILY_DEFAULT_CLAIM
 raise ValueError('The workload kind is invalid.')

def measured_fence(job):
 workload=job.get('workload')
 if not workload:return None
 profile=read(workload['profile'])
 route=profile.get('memory_route','diagnostic')
 if workload['kind']==PORT_KIND:
  production_port_case(profile,job)
  return PORT_FENCE
 if route=='diagnostic':return None
 if route!='measured_native' or workload['kind']!='minimal_native_tactic' or job['phase']!='native':
  raise ValueError('The measured route requires a minimal native job.')
 evidence=profile.get('observed_growth') or {}
 completion=profile.get('observed_completion') or {}
 if set(evidence)!={'runtime','accounting','aggregate'} or set(completion)!={'result','closure','release'}:
  raise ValueError('The measured route requires completed accounting and lifecycle bindings.')
 minimal_growth_claim(profile,job['target'])
 prior=read(evidence['runtime']);directory=Path(prior['job_output'])
 if Path(evidence['accounting']['path'])!=directory/'CPU-FINAL.json':
  raise ValueError('The measured route requires final accounting.')
 result,closure,release=(read(completion[k]) for k in ['result','closure','release'])
 for key,name in [('result','RESULT.json'),('closure','CLOSURE.json'),('release','RELEASE.json')]:
  if Path(completion[key]['path'])!=directory/name:raise ValueError('The measured lifecycle leaves its exact job.')
 if (result.get('module')!=job['target']['module'] or result.get('statement_sha256')!=job['target']['statement_sha256'] or
     result.get('proof_source_sha256')!=job['target']['source_sha256'] or result.get('normal_tactic_return') is not True or
     result.get('status') not in {'passed','native_open'} or result.get('resource_reason') or result.get('shared_infrastructure_failure')):
  raise ValueError('The measured native return is incomplete or names another boundary.')
 accounting=read(evidence['accounting']);aggregate=read(evidence['aggregate'])
 if result.get('CPU')!=accounting or result.get('aggregate_peak_bytes')!=accounting.get('aggregate_peak_bytes'):
  raise ValueError('The completed result differs from its final accounting.')
 if accounting.get('CPU_budget_enforced') is not False or not accounting.get('memory_events',{}).get('available'):
  raise ValueError('The completed measurement stopped or lacks memory events.')
 if any(accounting['memory_events']['counters'].get(k,0)>0 for k in ['oom','oom_kill','oom_group_kill']):
  raise ValueError('The completed measurement records an OOM.')
 if (closure.get('all_owned_actors_closed') is not True or closure.get('batch_identity')!=aggregate or
     not closure.get('actors') or any(a.get('ended') is not True for a in closure['actors']) or
     release.get('released') is not True or release.get('claim_key')!=closure.get('claim_key') or release.get('bytes',0)<=0):
  raise ValueError('The completed measurement lacks actor closure or claim release.')
 selected=rounded_claim(accounting['aggregate_peak_bytes'])
 if selected>32*GIB:raise ValueError('The measured fence exceeds the ordinary route. Use a diagnostic.')
 return selected

def job_fence(job):
 selected=measured_fence(job)
 return selected if selected is not None else fence(job['phase'])

def attempt_for_job(value,job):
 from copy import deepcopy
 validate_job(job)
 result=deepcopy(value);physical=job_fence(job)
 result['limits']['memory_bytes']=physical
 if job['phase']!='native':result['limits']['cpu_seconds']=None
 for row in result['scope_limits']:
  row['memory_bytes']=PARENT_FENCE if row['role']=='workloads' else physical
 return result

def profile_bindings(context):
 if not context:return []
 profile=read(context);values=[]
 if profile.get('kind')==PORT_KIND:
  authority=production_port_authority(profile)
  values += [profile['authority'],authority['completed_common_ready'],authority['source_packet']]
  if 'supplier_ready' in profile:
   from supplier_ready import validate
   values += validate(profile['supplier_ready'])['bindings']
 for key in ['observed_growth','observed_completion']:
  for value in (profile.get(key) or {}).values():bound(value);values.append(value)
 for value in values:bound(value)
 if 'supplier_ready' in profile:return list({(row['path'],row['sha256']):row for row in values}.values())
 return values

def apply_job(job,rows=(),workload=None):
 job=dict(job);phase=job['phase'];job['workload']=workload;physical=job_fence(job)
 basis=None;refused=[]
 if phase=='native' and (not workload or workload['kind']!='minimal_native_tactic'):basis,refused=select(rows,job['target'])
 claim=workload_claim(workload,job,basis)
 job.update(workload=workload,claim_bytes=claim,physical_fence_bytes=physical,completed_stock_measurement=basis,memory_refusals=refused)
 return job

def validate_job(job):
 physical=job_fence(job);basis=job.get('completed_stock_measurement')
 if job['phase']=='native' and basis:
  checked,reason=completed(basis['measurement'],job['target'])
  if not checked or any(checked.get(k)!=basis.get(k) for k in ['peak_bytes','scope','claim_bytes']):raise ValueError('A completed sizing basis is invalid: '+str(reason))
  expected=checked['claim_bytes']
 else:expected=physical
 expected=workload_claim(job.get('workload'),job,checked if job['phase']=='native' and basis else None)
 if job.get('physical_fence_bytes')!=physical or job.get('claim_bytes')!=expected:raise ValueError('The job claim or physical fence differs from its phase policy.')
 return expected

def admission_claim(policy):
 if 'memory_job' in policy:
  job=policy['memory_job'];expected=validate_job(job)
  if policy.get('physical_fence_bytes')!=job_fence(job) or policy.get('minimum_claim_bytes')!=expected:raise ValueError('Admission differs from its bound memory job.')
  return expected
 phase=policy.get('memory_phase','native');physical=fence(phase)
 if policy.get('physical_fence_bytes')!=physical:raise ValueError('The caller declares another physical fence.')
 requested=policy['minimum_claim_bytes']
 if type(requested) is not int or requested<=0:raise ValueError('The requested claim is invalid.')
 return max(requested,physical)

def environment(phase,claim_bytes=None,job=None):
 if job is not None:
  if job['phase']!=phase:raise ValueError('The environment phase differs from its memory job.')
  validate_job(job)
 physical=job_fence(job) if job is not None else fence(phase)
 measured=job is not None and measured_fence(job) is not None
 gib=physical//GIB
 claim_bytes=fence(phase) if claim_bytes is None else claim_bytes
 if type(claim_bytes) is not int or claim_bytes<=0:raise ValueError('The environment claim is invalid.')
 return {'ZESU_MEMORY_PHASE':phase,'ZESU_MODULE_CLAIM_BYTES':str(claim_bytes),'ZESU_BATCH_LIMIT':str(gib)+'G','ZESU_AGGREGATE_LIMIT':str(gib)+'G','ZESU_MODULE_LIMIT_GIB':str(gib),'ZESU_GATE_MODULE_LIMIT_GIB':str(gib),'ROCQ_MAX_PET_RSS_MB':str(gib*1024),'ZESU_SCOPE_CPU':'unlimited','ZESU_PROOF_CPU_LIMIT':'unlimited','ZESU_DIAGNOSTIC_PROBE':'0' if measured else '1','ZESU_PROBE_ISSUE':'' if measured else '10'}

def verification_bindings(row):
 if row.get('format')!='completed_stock_verification_repair_v1':return []
 supplement=read(row['verification_supplement']);restoration=read(supplement['restoration']);values=[row['verification_supplement']]
 def collect(value):
  if isinstance(value,dict):
   if isinstance(value.get('path'),str) and isinstance(value.get('sha256'),str):values.append({'path':value['path'],'sha256':value['sha256']})
   else:
    for child in value.values():collect(child)
  elif isinstance(value,list):
   for child in value:collect(child)
 collect(supplement);collect(restoration)
 found={}
 for value in values:
  if value['path'] in found and found[value['path']]!=value['sha256']:raise ValueError('Verification evidence has conflicting hashes.')
  found[value['path']]=value['sha256']
 return [{'path':path,'sha256':sha} for path,sha in found.items()]

def validate_unadmitted_retirement(receipt_binding,output):
 receipt=read(receipt_binding);output=Path(output)
 if receipt.get('all_exact_actors_ended') is not True or receipt.get('proof_started') is not False or receipt.get('claim_released_manually') is not False:raise ValueError('The exact retirement is incomplete.')
 if any(receipt.get('canonical_claims',{}).values()):raise ValueError('The retired requester held a claim.')
 started=json.loads((output/'STARTED.json').read_text());owner=receipt['owner']
 if any(started.get(k)!=owner.get(k) for k in ['pid','startticks']):raise ValueError('The retirement names another owner.')
 if (output/'BATCH-PROCESS.json').exists() or (output/'native/CALLS.json').exists():raise ValueError('The prior request reached proof work.')
 path=output/'ADMISSION.json'
 if path.exists() and any(row.get('admitted') is True for row in json.loads(path.read_text())):raise ValueError('An admitted run needs canonical closure and release.')
 for actor in receipt['actors']:
  path=Path('/proc')/str(actor['pid'])/'stat'
  try:
   fields=path.read_text().split(') ',1)[1].split()
   if int(fields[19])==actor['startticks'] and fields[0] not in {'Z','X'}:raise ValueError('A retired actor remains live.')
  except FileNotFoundError:pass
 return True
