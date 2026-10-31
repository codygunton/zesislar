"""Summarize retained chain artifacts. Never run a proof to classify a result."""
from pathlib import Path
from entry_chain import binding,digest,strict_loads
from entry_pilot_checker import complete_groups


def optional(path):
    return strict_loads(path.read_text()) if path.is_file() else None


def retained_groups(output,passed):
    output=Path(output);index=output/'native/first-residual/PRIVATE-INDEX.json'
    if index.exists():
        meta=strict_loads(index.read_text());row=meta['retained']
        path=row.get('residual',row.get('path'))
        if not isinstance(path,str) or not path:
            raise ValueError('The retained residual has no file path.')
        if row.get('residual') and row.get('path') and row['residual']!=row['path']:
            raise ValueError('The retained residual paths disagree.')
        export={'success':True,'path':path,'sha256':row['sha256']}
        groups=complete_groups(export)
        return groups,{**binding(Path(path)),'state_source':meta['state_source'],
                       'qualifier':meta['qualifier'],'private':True}
    if passed:return None,None
    pre=optional(output/'native/PRE-CALL-STATE.json')
    if pre:
        groups=complete_groups(pre['export'])
        return groups,{'path':pre['export']['path'],'sha256':pre['export']['sha256'],
                       'state_source':'retained_pre_call_state','private':True,
                       'qualifier':'The interrupted internal state is unavailable. This is the retained pre-call state.'}
    return None,None


def group_counts(groups):
    if groups is None:return None
    return {'active':len(groups['goals']),'focus_frames':len(groups['stack']),
            'frame_goals':sum(len(left)+len(right) for left,right in groups['stack']),
            'shelves':len(groups['shelf']),'given_up':len(groups['given_up'])}


def summarize(output,job,result):
    output=Path(output);progress=optional(output/'native/PROGRESS.json') or {}
    passed=result.get('success') is True
    receipts=result.get('native_receipts',{})
    route=job.get('native_route')
    if route and job['phase']=='native':
        from native_route import authority_body
        expected_body=authority_body(route)
        pre=optional(output/'native/PRE-CALL-STATE.json')
        if pre and pre.get('requested_body')!=expected_body:raise ValueError('The retained native request differs from its authority.')
        if passed:
            row=receipts.get('block',{})
            if row.get('native_route')!=route or row.get('native_tactic')!=expected_body[:-1]:
                raise ValueError('The native acceptance receipt differs from its reviewed route.')
    if passed and job['phase']=='native':
        row=receipts.get('block',{})
        if (row.get('statement_sha256')!=job['target']['statement_sha256']
            or row.get('compile_file_success') is not True or row.get('verification_method')!='module_m'
            or row.get('assumptions')!=[]):
            raise ValueError('A passing block lacks its exact native acceptance fields.')
        groups=complete_groups(row['final_export'])
        if any(groups.values()):raise ValueError('A passing block retains kernel obligations.')
        for name in ['source','object']:
            if digest(row[name])!=row[name+'_sha256']:raise ValueError('A passing native artifact changed.')
        state={'path':row['final_export']['path'],'sha256':row['final_export']['sha256'],
               'state_source':'successful_command_returned_state','private':True,'qualifier':'Empty groups after the native tactic.'}
    else:
        groups,state=retained_groups(output,passed)
    errors=[]
    for name in ['native/WORKER-FAILURE.json','CONTROLLER-FAILURE.json','growth/FAILURE.json','native/NATIVE-ERROR.json']:
        path=output/name
        if path.exists():errors.append(binding(path))
    native_error=optional(output/'native/NATIVE-ERROR.json') or {}
    command_error=native_error.get('complete_error_result',{})
    infrastructure=bool(result.get('observer_failure')) or (output/'native/INFRASTRUCTURE-FAILURE.json').exists()
    resource=None
    final=optional(output/'growth/STATUS.json') or {}
    events=final.get('memory_events',{})
    if events.get('oom_kill',0)>0 or events.get('oom_group_kill',0)>0:resource='memory'
    if command_error.get('reason') in {'timeout','memory_exhausted'}:resource=command_error['reason']
    counts=group_counts(groups)
    returned=state and state['state_source'] in {'successful_command_returned_state','returned_error_state'}
    nonempty=counts and any(counts[name] for name in ['active','frame_goals','shelves','given_up'])
    if passed:status='passed'
    elif resource:status='resource_stopped'
    elif infrastructure:status='infrastructure_failed'
    elif returned and nonempty and progress.get('phase')=='native_search':status='native_open'
    elif progress.get('phase') in {'native_search','Qed','native_compile','exact_verification'}:status='unresolved'
    else:status='infrastructure_failed';infrastructure=True
    summary={'status':status,'last_phase':progress.get('phase','not_started'),
            'last_progress':progress,'group_counts':counts,'complete_state':state,
            'private_residual':state if not passed else None,'private_errors':errors,
            'resource_reason':resource,'shared_infrastructure_failure':bool(infrastructure or resource),
            'classification_qualification':'A pre-call fallback does not identify the internal stopping state.'}

    if route:summary['native_route']=route
    return summary
