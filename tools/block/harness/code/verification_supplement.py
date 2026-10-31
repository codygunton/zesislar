"""Read the exact native result and its verification-only repair. Start no process."""
from pathlib import Path
import hashlib,json,re
EMPTY=dict(active=0,focus_frames=0,frame_goals=0,shelves=0,given_up=0)
def check(value,message):
 if not value:raise ValueError(message)
def bound(row):
 path=Path(row['path'])
 check(hashlib.sha256(path.read_bytes()).hexdigest()==row['sha256'],'A supplement input changed: '+str(path))
 return path
def read(row):return json.loads(bound(row).read_text())
def groups(state):
 check(all(isinstance(state.get(k),list) for k in ['goals','stack','shelf','given_up']),'A returned group is missing.')
 frames=state['stack']
 check(all(isinstance(x,list) and len(x)==2 and all(isinstance(y,list) for y in x) for x in frames),'A focus frame is invalid.')
 return dict(active=len(state['goals']),focus_frames=len(frames),frame_goals=sum(len(a)+len(b) for a,b in frames),shelves=len(state['shelf']),given_up=len(state['given_up']))
def response(call):
 raw=call['raw_response'];check(raw.get('isError') is not True,'A raw tool call failed.')
 actual=raw.get('structuredContent')
 if actual is None:
  actual=json.loads(next(x['text'] for x in raw['content'] if x.get('type')=='text'))
 check(actual==call['result'],'A retained response differs from its raw response.')
 return actual
def lifecycle(output):
 closure=read({'path':str(output/'CLOSURE.json'),'sha256':hashlib.sha256((output/'CLOSURE.json').read_bytes()).hexdigest()})
 release=json.loads((output/'RELEASE.json').read_text())
 check(closure.get('all_owned_actors_closed') is True and all(x.get('ended') is True for x in closure.get('actors',[])),'An actor closure is incomplete.')
 check(release.get('released') is True and release.get('bytes',release.get('released_bytes',0))>0 and closure.get('claim_key')==release.get('claim_key'),'A claim release is incomplete.')
 return closure,release

def validate(binding,target,original_binding=None):
 s=read(binding)
 check(s.get('schema')=='native-exact-verification-supplement.v1','The supplement format is unsupported.')
 check(s.get('panel')=='MAIN' and s.get('key')==target['key'],'The supplement selects another row.')
 check(all(s['target'].get(k)==target.get(k) for k in ['module','theorem','source_sha256','statement_sha256']),'The supplement target differs.')
 if original_binding:check(s['original_result']==original_binding,'The supplement names another result.')
 original=read(s['original_result']);runtime=read(s['original_runtime']);read(s['original_top_runtime'])
 actual=runtime['target']['block']
 check(all(actual.get(k)==target.get(k) for k in ['module','source_sha256','statement_sha256']),'The original runtime target differs.')
 check(original.get('module')==target['module'] and original.get('statement_sha256')==target['statement_sha256'],'The original result target differs.')
 text=bound(s['source']).read_text();check(s['source']['sha256']==target['source_sha256'],'The source differs.')
 check('Ltac ' not in text and 'RuleScratchRules' not in text and 'checkpoint_' not in text and re.search(r'Proof\.\s*zesu_block\.\s*Qed\.',text),'The caller is not plain stock.')
 check(hashlib.sha256(target['statement'].encode()).hexdigest()==target['statement_sha256'] and target['statement'] in text,'The statement differs.')
 for k in ['compiled_object','checked_object']:bound(s[k])
 check(s['compiled_object']['sha256']==s['checked_object']['sha256'],'The checked object differs.')
 calls=read(s['raw_native_calls']);ni,qi=s['native_call_index'],s['Qed_call_index']
 native,qed=calls[ni],calls[qi];nr,qr=response(native),response(qed)
 check(native['tool']=='rocq_check' and native['arguments']['body']=='zesu_block.' and nr.get('success') is True and nr.get('proof_finished') is True,'The native call did not finish.')
 check(qi>ni and qed['tool']=='rocq_check' and qed['arguments']['body']=='Qed.' and qed['arguments']['from_state']==nr['state_id'] and qr.get('success') is True,'Qed did not finish on the returned state.')
 state=read(s['post_search_complete_state']);check(groups(state)==groups(state['kernel_groups'])==s['returned_group_counts']==EMPTY,'The returned state is open.')
 exports=[c for c in calls[ni+1:qi] if c['tool']=='rocq_complete_goals' and c['arguments'].get('from_state')==nr['state_id']]
 check(any(all(response(c).get(k)==s['post_search_complete_state'][k] for k in ['path','sha256']) for c in exports),'The state is not the native returned export.')
 physical=read(s['physical_compile']);physical_input=read(s['physical_input'])
 check(physical.get('returncode')==0 and physical.get('input')==s['physical_input'] and physical.get('physical_argv')==physical_input.get('physical_argv'),'The physical compile failed or differs.')
 check(all(physical_input['target'].get(k)==target[k] for k in ['module','theorem','source_sha256']) and physical_input.get('command_phase')=='native_compile','The physical compile selects another target.')
 repair_calls=read(s['module_m']['calls']);verify=repair_calls[s['module_m']['call_index']];vr=response(verify)
 check(verify['tool']=='rocq_verify' and vr==s['module_m']['result'] and vr.get('success') is True and vr.get('verification_method')=='module_m' and vr.get('assumptions')==[],'The exact verification failed.')
 check('apply '+target['module']+'.'+target['theorem']+'.' in verify['arguments']['proof'],'The verifier does not apply the exact theorem.')
 repair=read(s['repair_result']);repair_runtime=read(s['repair_runtime']);bound(s['module_m']['control_verification'])
 check(repair.get('status')=='passed' and repair.get('success') is True,'The repair did not pass.')
 check(not any(c['tool']=='rocq_compile_file' or c['tool']=='rocq_check' and c.get('arguments',{}).get('body')=='zesu_block.' for c in repair_calls),'The repair repeated native proof work.')
 for key in ['repair_closure','repair_release']:read(s[key])
 lifecycle(Path(s['repair_result']['path']).parent);lifecycle(Path(s['original_result']['path']).parent)
 restore=read(s['restoration'])
 check(restore.get('complete_returned_groups')==s['post_search_complete_state'] and restore.get('original_object')==s['compiled_object'] and restore.get('native_search_repeated') is False,'The restoration boundary differs.')
 original_workspace=Path(s['original_runtime']['path']).parent/'workspace'
 repair_workspace=Path(s['repair_runtime']['path']).parent/'workspace'
 def flags(config,workspace):
  prefix=str(workspace.resolve())
  return ['$OWNED'+arg[len(prefix):] if arg==prefix or arg.startswith(prefix+'/') else arg for arg in config['physical_flags']]
 check(flags(runtime,original_workspace)==flags(repair_runtime,repair_workspace),'The repair compiler flags differ.')
 check((repair_workspace/repair_runtime['module_files'][target['module']]).with_suffix('.vo').resolve()==Path(s['checked_object']['path']).resolve(),'The verifier uses another object.')
 for row in restore['matching_dependency_pairs']:
  for key,suffix in [('source','.v'),('object','.vo')]:
   bound(row[key])
   for config,workspace in [(runtime,original_workspace),(repair_runtime,repair_workspace)]:
    path=(workspace/config['module_files'][row['module']]).with_suffix(suffix)
    check(hashlib.sha256(path.read_bytes()).hexdigest()==row[key]['sha256'],'A repair dependency differs: '+row['module'])
 check(s.get('native_search_repeated') is False and s.get('native_compilation_repeated') is False,'The supplement repeated proof work.')
 cpu=original.get('CPU') or {};peak=original.get('aggregate_peak_bytes')
 check(original.get('final_memory_accounting_available') is True and cpu.get('final_memory_accounting_available') is True and type(peak) is int and peak>0 and cpu.get('aggregate_peak_bytes')==peak==s.get('completed_native_peak_bytes'),'Final native accounting is missing.')
 check(not original.get('resource_reason') and not any((cpu.get('memory_events') or {}).get('counters',{}).get(k,0)>0 for k in ['oom','oom_kill','oom_group_kill']),'The native aggregate hit a resource limit.')
 return {'binding':binding,'original_status':original['status'],'effective_status':'closed','returned_groups':EMPTY,'complete_state':s['post_search_complete_state'],'repair_CPU_seconds':(repair.get('CPU') or {}).get('cpu_seconds'),'repair_peak_bytes':repair.get('aggregate_peak_bytes'),'native_peak_bytes':peak,'native_CPU':cpu,'physical_compile':s['physical_compile'],'original_result':s['original_result'],'original_runtime':s['original_runtime'],'scope':cpu['scope']}
