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

def completed_header_transition(row,target):
 if set(row)!={'format','route','module','native_source','statement_sha256','result','closure','release','baseline','authority'}:
  return None,'The header-transition measurement has invalid fields.'
 if row['baseline'].get('sha256')!=PORT_HEADER_BASELINE_SHA256:
  return None,'The header-transition baseline is not approved.'
 baseline=read(row['baseline'])
 if (baseline.get('schema')!='port.v32.old-eight-closure-baseline.v1' or
     baseline.get('accepted_closed_count')!=8 or baseline.get('all_sixteen_outcomes_complete') is not False):
  return None,'The header-transition baseline inventory differs.'
 expected=next((value for value in [PORT_EFFECTIVE_AUTHORITY,PORT_EFFECTIVE_AUTHORITY_23]
                if row['authority'].get('sha256')==value['sha256']),None)
 if expected is None or not relocated_authority(row['authority'],expected,
      ('/home/cody/zesislar/_build/agents/worker-build-2/PORT-v33-effective-overrides-authority-v1/PORT-FAMILY-AUTHORITY-22.json',
       '/home/cody/zesislar/_build/agents/worker-build-2/PORT-v33-effective-overrides-authority-v1/PORT-FAMILY-AUTHORITY-23.json')):
  return None,'The header-transition authority is not approved.'
 matches=[value for value in baseline['rows'] if value.get('status')=='closed'
          and value.get('accepted_closed') is True and value.get('module')==target.get('module')]
 if len(matches)!=1 or matches[0]['block'] not in baseline['must_remain_closed']:
  return None,'The header-transition case lacks an accepted closure.'
 prior=matches[0]
 cases=[value for value in read(row['authority'])['cases'] if value['block']==prior['block']]
 if len(cases)!=1:return None,'The header-transition case is not authorized.'
 case=cases[0]
 if (case['module']!=target.get('module') or case['pc']!=target.get('pc') or
     case['source']['sha256']!=target.get('source_sha256') or
     case['statement_sha256']!=target.get('statement_sha256') or
     row['module']!=target.get('module') or row['statement_sha256']!=target.get('statement_sha256')):
  return None,'The header-transition target differs.'
 old=prior['source_checks']['caller'];new=bound(row['native_source'])
 if (row['native_source']['sha256']!=target['source_sha256'] or
     prior['source_checks']['statement_sha256']!=target['statement_sha256']):
  return None,'The header-transition source or statement differs.'
 text=new.read_bytes();line=b'Require Import ZesuSsz.Automation.EffectiveOverrides.\n'
 if (not text.startswith(b'Require Import ZesuSsz.Automation.All.\n') or
     text.count(line)!=1 or text.replace(line,b'',1)!=bound(old).read_bytes()):
  return None,'The header transition changes more than the approved import.'
 if (row['route']!='stock_zesu_block' or row['result']!=prior['job_result'] or
     row['closure']!=prior['lifecycle']['closure'] or row['release']!=prior['lifecycle']['release']):
  return None,'The header-transition result or lifecycle differs.'
 predecessor=dict(route=row['route'],module=row['module'],native_source=old,
     statement_sha256=row['statement_sha256'],result=row['result'],closure=row['closure'],release=row['release'])
 checked,reason=completed(predecessor,dict(target,source_sha256=old['sha256']))
 if checked is None:return None,reason
 result=read(row['result']);accounting=read(prior['costs']['CPU_receipt'])
 peak=checked['peak_bytes']
 if (result.get('status')!='passed' or result['CPU']!=accounting or
     accounting.get('aggregate_peak_bytes')!=peak or prior['costs']['peak_bytes']!=peak):
  return None,'The header-transition peak or final accounting differs.'
 claim=(3*peak+1)//2
 if claim>PORT_FENCE:return None,'The header-transition claim exceeds its physical fence.'
 return dict(checked,measurement=row,claim_bytes=claim,formula='ceil(3 * completed_aggregate_peak_bytes / 2)',
     qualification='Completed v3.2 OLD peak across the approved header-only transition. Candidate performance is unmeasured.'),None

def header_transition_bindings(row):
 if row.get('format')=='completed_stock_v34_pilot_v1':
  return [row[name] for name in ['targets','authority','original_source','accounting','native_rules','normalization_policy','completed_authority']]
 if row.get('format')!='completed_stock_header_transition_v1':return []
 baseline=read(row['baseline'])
 prior=next(value for value in baseline['rows'] if value.get('status')=='closed' and value['module']==row['module'])
 return [row['baseline'],row['authority'],baseline['inventory'],baseline['source_transition'],baseline['header_successors'],
     prior['source_checks']['caller'],prior['costs']['CPU_receipt'],prior['costs']['search_origin'],
     prior['costs']['search_end'],prior['calls'],read(row['result'])['complete_state']]

def completed(row,target):
 if row.get('format')=='completed_stock_v33_open_v1':return completed_v33_open(row,target)
 if row.get('format')=='completed_stock_v34_pilot_v1':return completed_v34_pilot(row,target)
 if row.get('format')=='completed_stock_header_transition_v1':return completed_header_transition(row,target)
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
PORT_FULL_FENCE_BOOKING='full_physical_fence'
PORT_HEADER_PEAK_BOOKING='completed_header_transition_peak'
PORT_V34_PEAK_BOOKING='completed_pilot_peak'
PORT_V34_TARGETS={'path':str(Path(__file__).resolve().parents[1]/'policies'/'PORT-V34-TARGETS16.json'),
 'sha256':'3df54454cb2ca9337d0441e51f4ad3ef1fcc4bab54285d37301cf0d12a90fd12'}
PORT_6974_RENDER_REPAIR={'path':str(Path(__file__).resolve().parents[1]/'policies'/'PORT-6974-RENDERING-REPAIR.json'),
 'sha256':'54b8f36288c9f5fbe09bcaec9285ecaa72416d97692948d71744f0984b21f157'}
PORT_V34_RULES_SHA256='4620ed01bfaca15aae958fb7523e964dcbcfa58d8d4920fc0929285090f70488'
PORT_V34_POLICY_SHA256='df435e39840983dfa6ff3d96ba83a33b90389d2aafb0f8ef0b21094d93d82def'
PORT_V34_COMPLETED={'path':str(Path(__file__).resolve().parents[1]/'policies'/'PORT-V34-COMPLETED-PEAKS.json'),
 'sha256':'197eace1bdfce16dc232b9523fd1d711ba26b897f49637a1a195b51d1ca7db44'}
PORT_V34_BANKS={'path':str(Path(__file__).resolve().parents[1]/'policies'/'PORT-V34-ENTRY-BANKS.json'),
 'sha256':'b4c433d68c29b34f4bcac58cda0c701524531808df91bf176a1cae3a1926e0ed'}
PORT_V34_NEW={'path':str(Path(__file__).resolve().parents[1]/'policies'/'PORT-V34-NEW6A00.json'),
 'sha256':'30838486fc2c14ce148cc7be3ca88aa97c01c631bbe02a8cc58884a379e09ef0'}
PORT_HEADER_BASELINE_SHA256='b37cc0a5b86690de7f65245ebdfa9992be562af8a204ab9238e3ac85630dbd0c'
PORT_AUTHORITY={'path': str(Path(__file__).resolve().parents[1]/'policies'/'PORT-FAMILY-AUTHORITY-22.json'), 'sha256': 'ea88c0e9eab9e6e720e7fc2500407c065d82fd7a0feb12658783d4a761c79917'}
PORT_AUTHORITY_23={'path': str(Path(__file__).resolve().parents[1]/'policies'/'PORT-FAMILY-AUTHORITY-23.json'), 'sha256': 'dbeedb2c4fcdc916939a9c5fc9ced3d07bc619244c1d8b41bfc91aacfb5052bd'}
PORT_EFFECTIVE_AUTHORITY={'path': str(Path(__file__).resolve().parents[1]/'policies'/'PORT-EFFECTIVE-OVERRIDES-AUTHORITY-22.json'), 'sha256': '35c7e4a44203e761cb286bff7d95e83d81e08567bdb5dd0323dcd9667ffd8052'}
PORT_EFFECTIVE_AUTHORITY_23={'path': str(Path(__file__).resolve().parents[1]/'policies'/'PORT-EFFECTIVE-OVERRIDES-AUTHORITY-23.json'), 'sha256': '9952675250ea9828e18a1f65741aeede06c9df7689f647da8375470862768bb1'}
PORT_EFFECTIVE_EXTENSION={'path': str(Path(__file__).resolve().parents[1]/'policies'/'PORT-EFFECTIVE-OVERRIDES-EXTENSION.json'), 'sha256': '2f7f180cbad4da9c40c674c3a94a9d21e6f4fc9f1605300457ebf0c2ff5a8932'}
PORT_HELDOUT_AUTHORITY={'path': str(Path(__file__).resolve().parents[1]/'policies'/'PORT-HELDOUT-RUN2-AUTHORITY.json'), 'sha256': '6133fc1d79d1ebc794e77e4ea366ce61bd73444b919d7924c7ea04e67d053c29'}
PORT_HELDOUT_AUTHORITY_78={'path': str(Path(__file__).resolve().parents[1]/'policies'/'PORT-HELDOUT-RUN2-AUTHORITY-78.json'), 'sha256': '91772fc69bc3c82ab81d3bdfdc0fad4d8c766390f6c63204788a1def28b5ded2'}
PORT_HELDOUT_MEMORY_AUTHORITY={'path': str(Path(__file__).resolve().parents[1]/'policies'/'PORT-HELDOUT-RUN2-AUTHORITY-78-MEMORY.json'), 'sha256': '126f646885ba8b8a9fcd733037757f68bd4260d847a30031c331a134125fa8d3'}
HELDOUT_MEMORY_BOOKING={'unmeasured':'full_physical_fence','measured':'max(1GiB,ceil(1.5*completed_aggregate_peak_bytes))','maximum_live_cases_per_kind':2,'kind_field':'score_group','admission_resume_below_bytes':150*GIB}
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

def rendering_repair(binding):
 if not relocated_authority(binding,PORT_6974_RENDER_REPAIR):
  raise ValueError('The native rendering repair is not approved.')
 value=read(binding)
 if (value.get('schema')!='port.native-rendering-repair.v1' or value.get('block')!='800d6974'
     or value.get('claim_bytes')!=PORT_FENCE or value.get('physical_fence_bytes')!=PORT_FENCE
     or value.get('native_body')!='zesu_block.' or value.get('contract_changed') is not False):
  raise ValueError('The native rendering repair policy differs.')
 for row in value['originating_definitions']:bound(row)
 receipt=read(value['rendering_receipt'])
 if receipt.get('tokens_preserved') is not True or receipt.get('source_types_preserved_exactly') is not True:
  raise ValueError('The native rendering repair lacks its originating declaration check.')
 return value

def rendering_case(profile,case):
 if 'rendering_repair' not in profile:return case
 repair=rendering_repair(profile['rendering_repair'])
 if (case['block']!=repair['block'] or case['module']!=repair['module'] or case['pc']!=repair['pc']
     or case['statement_sha256']!=repair['original_statement_sha256']):
  raise ValueError('The rendering repair names another native target.')
 if profile.get('memory_booking') not in {PORT_FULL_FENCE_BOOKING,PORT_V34_PEAK_BOOKING}:
  raise ValueError('The repaired native requires full-fence booking.')
 variant=repair['variants']['v3.4' if v34_profile(profile) else 'v3.2']
 if bound(case['source']).read_bytes()!=bound(variant['previous_source']).read_bytes():
  raise ValueError('The rendering repair names another original caller.')
 bound(variant['corrected_source'])
 return dict(case,source=variant['corrected_source'],statement_sha256=repair['corrected_statement_sha256'])

def v34_target(binding,target,block,repair_binding=None):
 if not relocated_authority(binding,PORT_V34_TARGETS):
  raise ValueError('The v3.4 pilot inventory is not authorized.')
 rows=[row for row in read(binding)['rows'] if row['key']==block]
 if len(rows)==1 and repair_binding is not None:
  repair=rendering_repair(repair_binding)
  if block!=repair['block'] or rows[0]['statement_sha256']!=repair['original_statement_sha256']:
   raise ValueError('The rendering repair changes another pilot target.')
  rows=[dict(rows[0],statement_sha256=repair['corrected_statement_sha256'],
             source_sha256=repair['variants']['v3.2']['corrected_source']['sha256'])]
 if len(rows)!=1 or any(rows[0][key]!=target.get(key) for key in ['module','pc','statement_sha256']):
  raise ValueError('The v3.4 pilot target differs from the public inventory.')
 return rows[0]

def v34_native_caller(rules,policy,source):
 if (not isinstance(rules,dict) or rules.get('sha256')!=PORT_V34_RULES_SHA256 or
     not isinstance(policy,dict) or policy.get('sha256')!=PORT_V34_POLICY_SHA256):
  raise ValueError('The v3.4 carrier or normalization policy is not approved.')
 bound(rules)
 if read(policy)!={'hook_enabled':False,'database':'zesu_entry_normalize','registrations':[rules]}:
  raise ValueError('The v3.4 policy does not bind its exact inert carrier.')
 from scratch_statement import source_statement
 path=bound(source);original=path.read_text();spec=source_statement(path,'zesu_block.')
 offset=len(spec['prefix'])+len(spec['statement'])+len(spec.get('pre_proof_commands',''))
 line='Require Import ZesuSsz.Evidence.RuleScratchRules.\n'
 if line in original or original[offset:offset+6]!='Proof.':
  raise ValueError('The approved v3.4 import frontier differs.')
 return (original[:offset]+line+original[offset:]).encode()

def v34_completed_authority(binding):
 if not relocated_authority(binding,PORT_V34_COMPLETED):
  raise ValueError('The completed peak authority is not approved.')
 value=read(binding)
 if (value.get('schema')!='port.v34.completed-peak-authority.v1' or
     value.get('targets_sha256')!=PORT_V34_TARGETS['sha256']):
  raise ValueError('The completed peak authority names another inventory.')
 return value

def v34_profile(profile):
 return profile.get('memory_booking')==PORT_V34_PEAK_BOOKING or 'comparison_authority' in profile

def v34_comparison(profile):
 if not relocated_authority(profile.get('comparison_authority'),PORT_V34_NEW):
  raise ValueError('The NEW6a00 comparison authority is not approved.')
 value=read(profile['comparison_authority'])
 if (value.get('schema')!='port.v34.new-comparison-authority.v1' or value.get('variant')!='NEW6a00' or
     value.get('claim_bytes')!=PORT_FENCE or value.get('physical_fence_bytes')!=PORT_FENCE):
  raise ValueError('The NEW6a00 comparison policy differs.')
 return value

def v34_case_source(profile,case):
 return v34_comparison(profile)['caller'] if 'comparison_authority' in profile else case['source']

def v34_bank_sources(profile,job):
 if not relocated_authority(profile.get('bank_authority'),PORT_V34_BANKS):
  raise ValueError('The v3.4 declaration bank authority is not approved.')
 bank=read(profile['bank_authority'])
 if 'comparison_authority' in profile:
  comparison=v34_comparison(profile)
  if (job['key']!=comparison['block'] or any(job['target'].get(key)!=comparison[key]
      for key in ['module','pc','statement_sha256']) or comparison['banks']['sha256']!=profile['bank_authority']['sha256']):
   raise ValueError('The NEW6a00 target or declaration bank differs.')
  names=bank['case_modules']['NEW:800d6a00'];sources=bank['NEW6a00_sources']
 else:
  v34_target(profile['pilot_targets'],job['target'],job['key'],profile.get('rendering_repair'))
  names=bank['case_modules'][job['key']];sources=dict(bank['OLD_sources'])
  if job['key'] in bank['retention_cases']:sources.update(bank['retention_sources'])
 selected={name:sources[name] for name in names}
 for row in read(bank['shared_overlay']):
  if row['module'].startswith('ZesuSsz.Automation.'):
   if row['module'] in selected and selected[row['module']]!=row['sha256']:
    raise ValueError('The shared v3.4 overlay conflicts with its declaration bank.')
   selected[row['module']]=row['sha256']
 return [dict(module=name,sha256=sha) for name,sha in sorted(selected.items())]

def completed_v34_pilot(row,target):
 required={'format','route','block','module','native_source','original_source',
  'statement_sha256','result','accounting','closure','release','targets','authority','native_rules','normalization_policy','completed_authority'}
 if set(row)!=required:return None,'The v3.4 completed measurement has invalid fields.'
 prior=v34_target(row['targets'],target,row['block'])
 if prior['key']=='800d6974':return None,'The v3.4 6974 pilot requires full-fence booking.'
 approved=[item for item in v34_completed_authority(row['completed_authority'])['rows'] if item['block']==row['block']]
 if (len(approved)!=1 or approved[0]['module']!=prior['module'] or
     approved[0]['statement_sha256']!=prior['statement_sha256'] or
     any(row[name]['sha256']!=approved[0]['receipt_sha256'][name] for name in ['result','accounting','closure','release'])):
  return None,'The completed v3.2 receipt is not authorized for this pilot.'
 if not relocated_authority(row['authority'],PORT_EFFECTIVE_AUTHORITY_23):
  return None,'The v3.4 completed measurement authority is not approved.'
 matches=[case for case in read(row['authority'])['cases'] if case['block']==prior['key']]
 if (len(matches)!=1 or matches[0]['module']!=target['module'] or
     row['module']!=target['module'] or row['statement_sha256']!=target['statement_sha256']):
  return None,'The v3.4 current caller differs from its approved authority.'
 if row['original_source']['sha256']!=prior['source_sha256']:
  return None,'The completed v3.2 caller differs from the public inventory.'
 old=bound(row['original_source']).read_bytes();base=bound(matches[0]['source']).read_bytes()
 line=b'Require Import ZesuSsz.Automation.EffectiveOverrides.\n'
 if base.count(line)!=1 or base.replace(line,b'',1)!=old:
  return None,'The v3.4 caller changes more than the approved header.'
 expected=v34_native_caller(row['native_rules'],row['normalization_policy'],matches[0]['source'])
 if (bound(row['native_source']).read_bytes()!=expected or
     row['native_source']['sha256']!=target['source_sha256']):
  return None,'The v3.4 caller differs from the exact public rules import.'
 predecessor={key:row[key] for key in ['route','module','statement_sha256','result','closure','release']}
 predecessor['native_source']=row['original_source']
 version=approved[0]['provenance_version']
 if version=='v3.1' and row['block'] in {'800d6a14','800d6ab4'}:
  result,accounting,closure,release=(read(row[name]) for name in ['result','accounting','closure','release'])
  peak=result.get('aggregate_peak_bytes')
  if (result.get('status')!='unresolved' or result.get('module')!=target['module'] or
      result.get('statement_sha256')!=target['statement_sha256'] or
      result.get('resource_reason') or result.get('shared_infrastructure_failure') or
      result.get('final_memory_accounting_available') is not True or
      accounting.get('final_memory_accounting_available') is not True or
      type(peak) is not int or peak<=0 or accounting.get('aggregate_peak_bytes')!=peak or
      any((accounting.get('memory_events') or {}).get('counters',{}).get(key,0)>0
          for key in ['oom','oom_kill','oom_group_kill']) or
      closure.get('all_owned_actors_closed') is not True or release.get('released') is not True or
      release.get('bytes')!=8*GIB or not accounting.get('scope')):
   return None,'The approved v3.1 peak or lifecycle is incomplete.'
  checked={'peak_bytes':peak,'scope':accounting['scope'],'memory_metric':'aggregate_memory.peak',
   'client_server_allowance_bytes':0}
  reason=None
 elif version=='v3.2':checked,reason=completed(predecessor,dict(target,source_sha256=prior['source_sha256']))
 else:return None,'The completed peak provenance is not approved.'
 if checked is None:return None,reason
 if checked['peak_bytes']!=approved[0]['peak_bytes']:
  return None,'The completed v3.2 peak differs from its approved receipt.'
 result=read(row['result']);accounting=read(row['accounting'])
 if (Path(row['accounting']['path']).parent!=Path(row['result']['path']).parent or
     Path(row['accounting']['path']).name!='CPU-FINAL.json' or result['CPU']!=accounting):
  return None,'The completed v3.2 accounting receipt differs.'
 claim=max(GIB,(3*checked['peak_bytes']+1)//2)
 if claim>PORT_FENCE:return None,'The completed v3.2 peak exceeds the approved v3.4 fence.'
 return dict(checked,measurement=row,claim_bytes=claim,
  formula='max(1GiB,ceil(1.5*completed_aggregate_peak_bytes))',provenance_version=version,
  qualification='Approved '+version+' OLD aggregate peak. Candidate performance is unmeasured. Memory evidence does not establish proof acceptance.'),None

PORT_V33_OPEN_BOOKING='completed_open_pilot_peak'
PORT_V33_OPEN_AUTHORITY={'path':str(Path(__file__).resolve().parents[1]/'policies'/'PORT-V33-OPEN-AUTHORITY.json'),
 'sha256':'7d59bc18d574bb9eed93e3ef3274e00015e40bf92db767e4f75cbc54c0357df3'}

def v33_open_profile(profile):
 return profile.get('memory_booking')==PORT_V33_OPEN_BOOKING

def v33_open_authority(profile):
 if (set(profile)!={'schema','kind','authority','memory_route','memory_booking','supplier_ready'} or
     profile.get('schema')!='scratch.admission-profile.v1' or profile.get('kind')!=PORT_KIND or
     profile.get('memory_route')!='measured_native' or not v33_open_profile(profile) or
     not relocated_authority(profile.get('authority'),PORT_V33_OPEN_AUTHORITY)):
  raise ValueError('The v3.3 open-pilot profile is invalid.')
 value=read(profile['authority'])
 if (value.get('schema')!='port.v33.open-pilot-authority.v1' or value.get('rule_version')!='v3.3' or
     profile['supplier_ready']!=value['supplier_ready'] or value['physical_fence_bytes']!=PORT_FENCE or
     value['native_body']!='zesu_block.' or value['setup_order']!=[] or value['CPU_stops'] is not None):
  raise ValueError('The v3.3 open-pilot ruling differs.')
 bound(value['supplier_ready'])
 for row in value['production_sources']:bound(row)
 return value

def completed_v33_open(row,target):
 required={'format','route','block','module','native_source','statement_sha256','result','accounting','closure','release','authority'}
 if set(row)!=required or row['route']!='stock_zesu_block':return None,'The v3.3 open measurement has invalid fields.'
 if not relocated_authority(row['authority'],PORT_V33_OPEN_AUTHORITY):return None,'The v3.3 open measurement authority differs.'
 authority=read(row['authority']);matches=[r for r in authority['cases'] if r['block']==row['block']]
 if len(matches)!=1:return None,'The v3.3 open measurement case differs.'
 case=matches[0]
 if (any(case.get(k)!=target.get(k) for k in ['module','pc','statement_sha256']) or
     case['source']!=row['native_source'] or case['source']['sha256']!=target.get('source_sha256') or
     row['module']!=case['module'] or row['statement_sha256']!=case['statement_sha256'] or
     any(row[k]!=case['measurement'][k] for k in ['result','accounting','closure','release'])):
  return None,'The v3.3 open measurement names another boundary or receipt.'
 result,accounting,closure,release=(read(row[k]) for k in ['result','accounting','closure','release'])
 peak=case['peak_bytes'];claim=(3*peak+1)//2
 if (type(peak) is not int or peak<=0 or claim!=case['claim_bytes'] or claim>PORT_FENCE or
     result.get('aggregate_peak_bytes')!=peak or accounting.get('aggregate_peak_bytes')!=peak or
     result.get('CPU')!=accounting or closure.get('all_owned_actors_closed') is not True or
     release.get('released') is not True or release.get('claim_key')!=closure.get('claim_key')):
  return None,'The v3.3 open measurement lacks its completed accounting or closure.'
 if any(accounting.get('memory_events',{}).get('counters',{}).get(k,0)>0 for k in ['oom','oom_kill','oom_group_kill']):
  return None,'The v3.3 open measurement records an OOM.'
 return {'measurement':row,'peak_bytes':peak,'claim_bytes':claim,'scope':accounting.get('scope'),
  'formula':'ceil(3 * completed_peak_bytes / 2)','memory_metric':'aggregate_memory.peak',
  'qualification':'Approved cross-version completed peak. Memory evidence is not proof acceptance.'},None

def production_port_authority(profile):
 if v33_open_profile(profile):return v33_open_authority(profile)
 required={'schema','kind','authority','memory_route'}
 if not required<=set(profile)<=required|{'supplier_ready','memory_booking','pilot_targets','native_rules','normalization_policy','completed_peak_authority','bank_authority','comparison_authority','rendering_repair'} or profile.get('schema')!='scratch.admission-profile.v1' or profile.get('kind')!=PORT_KIND or profile.get('memory_route')!='measured_native':
  raise ValueError('The production PORT profile is invalid.')
 if 'memory_booking' in profile and profile['memory_booking'] not in (PORT_FULL_FENCE_BOOKING,PORT_HEADER_PEAK_BOOKING,PORT_V34_PEAK_BOOKING):
  raise ValueError('The PORT memory booking option is invalid.')
 extended=isinstance(profile['authority'],dict) and profile['authority'].get('sha256') in {PORT_AUTHORITY_23['sha256'],PORT_EFFECTIVE_AUTHORITY_23['sha256']}
 effective=isinstance(profile['authority'],dict) and profile['authority'].get('sha256') in {PORT_EFFECTIVE_AUTHORITY['sha256'],PORT_EFFECTIVE_AUTHORITY_23['sha256']}
 if profile.get('memory_booking')==PORT_HEADER_PEAK_BOOKING and not effective:
  raise ValueError('Header-transition sizing requires its exact approved authority.')
 if v34_profile(profile):
  if profile['authority'].get('sha256')!=PORT_EFFECTIVE_AUTHORITY_23['sha256'] or not relocated_authority(profile.get('pilot_targets'),PORT_V34_TARGETS):
   raise ValueError('The v3.4 sizing policy requires its exact public authority and inventory.')
  case=next(row for row in read(profile['authority'])['cases'] if row['block']=='800d6a00')
  v34_native_caller(profile.get('native_rules'),profile.get('normalization_policy'),v34_case_source(profile,case))
  if not relocated_authority(profile.get('bank_authority'),PORT_V34_BANKS):
   raise ValueError('The v3.4 declaration bank authority is not approved.')
  if 'comparison_authority' in profile:
   if profile['memory_booking']!=PORT_FULL_FENCE_BOOKING or 'completed_peak_authority' in profile:
    raise ValueError('The NEW6a00 comparison requires unmeasured full-fence booking.')
  else:v34_completed_authority(profile.get('completed_peak_authority'))
 elif set(profile)&{'pilot_targets','native_rules','normalization_policy','completed_peak_authority','bank_authority'}:raise ValueError('The v3.4 inputs require the v3.4 booking policy.')
 corrected=isinstance(profile['authority'],dict) and profile['authority'].get('sha256')==PORT_HELDOUT_MEMORY_AUTHORITY['sha256']
 heldout78=isinstance(profile['authority'],dict) and profile['authority'].get('sha256')==PORT_HELDOUT_AUTHORITY_78['sha256']
 heldout=corrected or heldout78 or isinstance(profile['authority'],dict) and profile['authority'].get('sha256')==PORT_HELDOUT_AUTHORITY['sha256']
 if heldout and 'memory_booking' in profile:
  raise ValueError('The full-fence option cannot change a blind PORT policy.')
 expected=PORT_HELDOUT_MEMORY_AUTHORITY if corrected else PORT_HELDOUT_AUTHORITY_78 if heldout78 else PORT_HELDOUT_AUTHORITY if heldout else PORT_AUTHORITY_23 if extended else PORT_AUTHORITY
 if effective:expected=PORT_EFFECTIVE_AUTHORITY_23 if extended else PORT_EFFECTIVE_AUTHORITY
 legacy_paths=('/home/cody/zesislar/_build/agents/worker-build-1/new6974-bindings291/extension002/PORT-FAMILY-AUTHORITY-23.json',) if extended else ('/home/cody/zesislar/_build/agents/worker-build-2/PORT-union-v2/matrix005-authority-v1/PORT-FAMILY-AUTHORITY-22.json', '/home/cody/zesislar/_build/agents/worker-build-2/PORT-matrix006-authority-v1/PORT-FAMILY-AUTHORITY-22.json')
 if effective:legacy_paths=('/home/cody/zesislar/_build/agents/worker-build-2/PORT-v33-effective-overrides-authority-v1/PORT-FAMILY-AUTHORITY-23.json' if extended else '/home/cody/zesislar/_build/agents/worker-build-2/PORT-v33-effective-overrides-authority-v1/PORT-FAMILY-AUTHORITY-22.json',)
 if not relocated_authority(profile['authority'],expected,legacy_paths):raise ValueError('The production PORT authority is not authorized.')
 authority=read(profile['authority'])
 if (authority.get('schema')!='port.production-stock-family-authority.v1' or
     authority.get('claim_bytes')!=(PORT_FENCE if corrected else 8*GIB) or authority.get('physical_fence_bytes')!=PORT_FENCE or
     authority.get('native_body')!='zesu_block.' or authority.get('setup_order')!=[] or
     authority.get('minimal_or_private_route') is not False or authority.get('fence_hit_retry') is not False):
  raise ValueError('The production PORT ruling differs.')
 if corrected and authority.get('memory_booking')!=HELDOUT_MEMORY_BOOKING:
  raise ValueError('The held-out memory ruling differs.')
 if heldout:
  from port_heldout_authority import validate
  validate(authority)
 else:
  cases=authority['cases']
  released_cases=cases[:-1] if extended else cases
  case_count=23 if extended else 22
  extension_binding=PORT_EFFECTIVE_EXTENSION if effective else PORT_EXTENSION
  extension_paths=('/home/cody/zesislar/_build/agents/worker-build-2/PORT-v33-effective-overrides-authority-v1/EXTENSION.json',) if effective else ('/home/cody/zesislar/_build/agents/worker-build-2/native-port-policy-v1/source014-authority22-caller002-extension/EXTENSION.json', '/home/cody/zesislar/_build/agents/worker-build-2/PORT-matrix006-authority-v1/EXTENSION.json')
  extension=read(extension_binding)
  read(extension['exit_queue'])
  if (extension.get('case_count')!=22 or not relocated_authority(authority.get('authority_extension'),extension_binding,extension_paths)
      or released_cases!=extension['original_cases']+extension['additional_cases']
      or len(cases)!=case_count or len({r['block'] for r in cases})!=case_count or len({r['module'] for r in cases})!=case_count):
   raise ValueError('The production PORT case set differs from the exact released inventory.')
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
 case=rendering_case(profile,rows[0])
 if target.get('pc')!=case['pc']:raise ValueError('The production PORT address differs.')
 expected=case['source']['sha256']
 if v34_profile(profile):
  v34_bank_sources(profile,job)
  expected=hashlib.sha256(v34_native_caller(profile['native_rules'],profile['normalization_policy'],v34_case_source(profile,case))).hexdigest()
 if target.get('source_sha256')!=expected or target.get('statement_sha256')!=case['statement_sha256']:
  raise ValueError('The production PORT source or statement differs.')
 if profile.get('memory_booking')==PORT_V34_PEAK_BOOKING:
  v34_target(profile['pilot_targets'],target,job['key'],profile.get('rendering_repair'))
 return authority,case

def workload_for_job(profile_binding,job,config):
 if not profile_binding:return None
 profile=read(profile_binding)
 if profile.get('schema')!='scratch.admission-profile.v1':raise ValueError('The admission profile is unsupported.')
 kind=profile.get('kind')
 if kind not in {FAMILY_KIND,FOCUSED_KIND,'minimal_native_tactic',PORT_KIND}:raise ValueError('The workload kind is unsupported.')
 if 'memory_booking' in profile and kind not in {PORT_KIND,FOCUSED_KIND}:raise ValueError('Full-fence booking requires a production PORT profile or a focused declaration profile.')
 if 'memory_booking' in profile and kind==FOCUSED_KIND:
  if profile['memory_booking']!=PORT_FULL_FENCE_BOOKING:raise ValueError('The declaration memory booking option is invalid.')
  if config.get('declarations_only') is not True:raise ValueError('Full-fence declaration booking requires declaration-only execution.')
  if job['phase']=='native' and job.get('ordered_modules',[])==[] and job.get('native_route') is None:return None
  if job['phase'] not in COMPILE_PHASES:raise ValueError('Full-fence declaration booking requires declaration-only execution.')
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
  v34=v34_profile(profile)
  if v34:
   source=actual(dict(path=str(workspace/modules[case['module']]),sha256=job['target']['source_sha256'],module=case['module']))
   if source.read_bytes()!=v34_native_caller(profile['native_rules'],profile['normalization_policy'],v34_case_source(profile,case)):
    raise ValueError('The staged v3.4 caller differs from its public import plan.')
   actual(dict(profile['native_rules'],module='ZesuSsz.Evidence.RuleScratchRules'))
   for row in v34_bank_sources(profile,job):
    if row['module'] not in modules:raise ValueError('A v3.4 semantic bank source is absent.')
    actual(dict(row,path=str(workspace/modules[row['module']])))
  else:source=actual(dict(case['source'],module=case['module']))
  text=source.read_text()
  forbidden=r'\b(?:Ltac2?|AllLegacy)\b' if v34 else r'\b(?:Ltac2?|RuleScratchRules|AllLegacy)\b'
  hand_seeded=v33_open_profile(profile) and case['bank']=='hand_seeded'
  if hand_seeded:forbidden=r'\b(?:Ltac2?|AllLegacy)\b'
  if (not hand_seeded and not text.startswith('Require Import ZesuSsz.Automation.All.\n')) or re.search(forbidden,text):
   raise ValueError('The production PORT caller is not plain production stock.')
  from scratch_statement import source_statement
  specification=source_statement(source,'zesu_block.')
  if hashlib.sha256(specification['statement'].encode()).hexdigest()!=case['statement_sha256']:
   raise ValueError('The production PORT declaration differs.')
  if 'rendering_repair' in profile:
   for row in rendering_repair(profile['rendering_repair'])['originating_definitions']:actual(row)
  if v33_open_profile(profile):
   for row in case['bank_sources']:
    if row['module'] not in modules:raise ValueError('The v3.3 open semantic bank source is absent.')
    actual(dict(row,path=str(workspace/modules[row['module']])))
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
 profile=read(workload['profile']);kind=profile.get('kind')
 if kind!=workload['kind']:raise ValueError('The workload profile kind changed.')
 if kind=='minimal_native_tactic':
  if job['phase']!='native' or job.get('native_route')!=actual['native_route']:
   raise ValueError('The minimal native job lost its reviewed authority.')
  return minimal_growth_claim(read(workload['profile']),job['target'])
 if kind==FOCUSED_KIND:
  if job['phase'] not in COMPILE_PHASES:raise ValueError('A focused check cannot execute native search.')
  if profile.get('memory_booking')==PORT_FULL_FENCE_BOOKING:
   if 'declaration_dag_booking' in job:
    from declaration_parallel_plan import booking_claim
    return booking_claim(job)
   return job_fence(job)
  return FOCUSED_CLAIM
 if kind==PORT_KIND:
  if v33_open_profile(profile):
   if basis is None or basis['measurement'].get('format')!='completed_stock_v33_open_v1':
    raise ValueError('The v3.3 open pilot requires its exact completed peak.')
   return basis['claim_bytes']
  if profile.get('memory_booking')==PORT_FULL_FENCE_BOOKING:return PORT_FENCE
  if profile.get('memory_booking')==PORT_V34_PEAK_BOOKING:
   v34_target(profile['pilot_targets'],job['target'],job['key'],profile.get('rendering_repair'))
   if job['key']=='800d6974':return PORT_FENCE
   if (basis is None or basis['measurement'].get('format')!='completed_stock_v34_pilot_v1' or
       basis['measurement']['block']!=job['key'] or
       basis['measurement']['targets']['sha256']!=profile['pilot_targets']['sha256']):
    raise ValueError('The v3.4 pilot requires its exact completed v3.2 measurement.')
   return basis['claim_bytes']
  if profile.get('memory_booking')==PORT_HEADER_PEAK_BOOKING:
   if basis is None or basis['measurement'].get('format')!='completed_stock_header_transition_v1':
    raise ValueError('Header-transition sizing requires an accepted completed measurement.')
   return basis['claim_bytes']
  if profile['authority']['sha256']!=PORT_HELDOUT_MEMORY_AUTHORITY['sha256']:return 8*GIB
  if basis is None:return PORT_FENCE
  if basis.get('memory_metric')!='aggregate_memory.peak':return PORT_FENCE
  peak=basis.get('peak_bytes')
  if type(peak) is not int or peak<=0:raise ValueError('A completed peak must be a positive integer.')
  claim=max(GIB,(3*peak+1)//2)
  if claim>PORT_FENCE:raise ValueError('The completed held-out peak requires a larger reviewed fence.')
  return claim
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
  if v33_open_profile(profile):
   values.extend([authority['retention_evidence'],authority['retention_proposal'],authority['measurement_authority']])
   for case in authority['cases']:
    values.append(case['source']);values.extend(case['measurement'][k] for k in ['result','accounting','closure','release'])
    if 'source_readiness' in case:values.append(case['source_readiness'])
  if v34_profile(profile):
   values.extend(profile[name] for name in ['pilot_targets','native_rules','normalization_policy','bank_authority'])
   values.append(profile['comparison_authority'] if 'comparison_authority' in profile else profile['completed_peak_authority'])
   bank=read(profile['bank_authority'])
   values.extend(bank[name] for name in ['shared_overlay','old_graph','new_graph','retention_authority','NEW6a00_authority'] if name in bank)
  if authority.get('blind_reporting') is True:
   values += [authority[key] for key in ['case_rebind','eql18_targets','frozen_manifest','declaration_evidence']]
   if 'raw60_targets' in authority:
    values += [authority[key] for key in ['raw60_targets','raw60_emission','raw60_refusal_checks']]
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
  workload=job.get('workload') or {}
  if workload.get('kind') in {PORT_KIND,FOCUSED_KIND} and read(workload['profile']).get('memory_booking')==PORT_FULL_FENCE_BOOKING:
   physical=job_fence(job)
   expected=job['claim_bytes'] if 'declaration_dag_booking' in job else physical
   if claim_bytes is not None and claim_bytes!=expected:
    raise ValueError('The environment claim differs from its bound declaration booking.' if 'declaration_dag_booking' in job else 'The environment claim differs from full-fence booking.')
   claim_bytes=expected
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
