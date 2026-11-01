"""Enforce only external scratch stops. Never change a tactic or CPU rlimit."""
from pathlib import Path
import json,re,subprocess,time
from contextvars import ContextVar
from copy import deepcopy
import os
from entry_chain import read_bound,binding,save
CPU_STOP_SECONDS=7200
SETUP_CPU_STOP_SECONDS=None
MEMORY_FENCE_BYTES=68719476736
CLAIM_REPORT_MULTIPLIER=2

_MONITOR_POLICY = ContextVar('validated_scratch_monitor_policy', default=None)


class _MonitorPolicy:
    """Freeze validated resource policy for one owned monitoring loop."""
    def __init__(self, memory_job, phase):
        from memory_policy import fence, job_fence, validate_job
        from port_native_policy import cpu_budgets
        self.job = deepcopy(memory_job)
        self.phase, self.pid = phase, os.getpid()
        if memory_job is not None:
            validate_job(memory_job)
        self.physical = job_fence(memory_job) if memory_job is not None else fence(phase)
        self.budgets = cpu_budgets(memory_job, CPU_STOP_SECONDS, SETUP_CPU_STOP_SECONDS)


def _policy(memory_job, phase=None):
    selected = _MONITOR_POLICY.get()
    if selected is not None:
        if (selected.pid != os.getpid() or selected.job != memory_job or
                phase is not None and selected.phase != phase):
            raise ValueError('The validated monitor job changed.')
        return selected
    return _MonitorPolicy(memory_job, phase or 'native')


def stop_reason(cpu_seconds,memory_bytes,claim_bytes,prior_cpu_seconds=0,*,phase='native',origin_cpu=None,end_cpu=None,memory_job=None):
    policy=_policy(memory_job,phase)
    if memory_bytes>=policy.physical:return 'external_memory_stop'
    search_budget,setup_budget=policy.budgets
    if phase=='native' and origin_cpu is not None:
        if cpu_seconds<origin_cpu:raise ValueError('The aggregate CPU counter precedes the search origin.')
        if end_cpu is None and search_budget is not None and cpu_seconds-origin_cpu>=search_budget:return 'external_CPU_stop'
        nonsearch=origin_cpu+max(0,cpu_seconds-end_cpu) if end_cpu is not None else origin_cpu
        if setup_budget is not None and nonsearch>=setup_budget:return 'external_setup_CPU_stop'
    elif setup_budget is not None and cpu_seconds>=setup_budget:return 'external_setup_CPU_stop'
    return None

def claim_report_required(memory_bytes,claim_bytes,*,family=False,peak_bytes=None,family_threshold_bytes=16*1024**3):
    if family:return max(memory_bytes,peak_bytes or 0)>family_threshold_bytes
    return memory_bytes>CLAIM_REPORT_MULTIPLIER*claim_bytes

def exact_aggregate(identity,memory_fence_bytes=MEMORY_FENCE_BYTES,*,memory_job=None):
    from memory_policy import NATIVE_FENCE
    if memory_job is not None:
        if memory_fence_bytes!=_policy(memory_job).physical:raise ValueError('The aggregate differs from its bound memory job.')
    elif memory_fence_bytes!=NATIVE_FENCE:raise ValueError('A measured aggregate requires its bound memory job.')
    path=Path(identity['aggregate_path'])
    if not re.fullmatch(r'zesuworkloads-aggregate[0-9]+p[0-9]+r[0-9]+\.slice',path.name):
        raise ValueError('The scratch aggregate name is invalid.')
    if path.parent.name != 'zesuworkloads.slice':
        raise ValueError('The scratch aggregate is outside the shared workload parent.')
    if ((path.parent/'memory.max').read_text().strip() != '187904819200' or
            (path.parent/'memory.swap.max').read_text().strip() != '0'):
        raise ValueError('The shared workload parent lacks its exact memory fence.')
    if ((path/'memory.max').read_text().strip()!=str(memory_fence_bytes) or
            (path/'memory.swap.max').read_text().strip()!='0'):
        raise ValueError('The owned aggregate lacks its selected physical fence.')
    st=path.stat()
    if (st.st_dev,st.st_ino)!=(identity['aggregate_device'],identity['aggregate_inode']):
        raise ValueError('The scratch aggregate identity changed.')
    return path

def memory_events(group):
    try:
        return {'available':True,'counters':{key:int(value) for key,value in
            (line.split() for line in (group/'memory.events').read_text().splitlines())}}
    except (OSError,ValueError) as error:
        return {'available':False,'reason':str(error)}

def sample_aggregate(group):
    raw=dict(line.split() for line in (group/'cpu.stat').read_text().splitlines())
    return {'CPU_seconds':int(raw['usage_usec'])/1e6,'raw_cpu_stat':raw,
        'memory_current_bytes':int((group/'memory.current').read_text()),
        'memory_peak_bytes':int((group/'memory.peak').read_text()),
        'memory_events':memory_events(group)}

def job_aggregate(identity,out):
    from memory_policy import job_fence,validate_job
    runtime=read_bound(binding(Path(out)/'RUNTIME.json'));job=runtime['canonical_admission']['memory_job']
    validate_job(job)
    return exact_aggregate(identity,job_fence(job),memory_job=job)


def record_search_origin(out,operation_started_ns,arguments,native_route=None):
    out=Path(out);destination=out/'SEARCH-CPU-ORIGIN.json'
    if destination.exists():raise ValueError('The native search origin already exists.')
    from native_route import authority_body
    expected_body=authority_body(native_route) if native_route else 'zesu_block.'
    if arguments.get('body')!=expected_body:raise ValueError('The bounded native command changed.')
    identity=read_bound(binding(out/'BATCH-IDENTITY.json'));group=job_aggregate(identity,out)
    sample=sample_aggregate(group)
    from port_native_policy import cpu_budgets
    runtime_path=out/'RUNTIME.json'
    memory_job=read_bound(binding(runtime_path))['canonical_admission']['memory_job'] if runtime_path.exists() else None
    search_budget,setup_budget=cpu_budgets(memory_job,CPU_STOP_SECONDS,SETUP_CPU_STOP_SECONDS)
    row={'schema':'scratch.native-search-cpu-origin.v1','aggregate':identity,
        'operation_started_ns':operation_started_ns,'tool':'rocq_check','arguments':arguments,
        'CPU_seconds':sample['CPU_seconds'],'raw_cpu_stat':sample['raw_cpu_stat'],
        'setup_CPU_seconds':sample['CPU_seconds'],'search_budget_CPU_seconds':search_budget,
        'setup_budget_CPU_seconds':setup_budget,
        'prerequisites_excluded':True,'scope':'Exact owned aggregate immediately before native RPC dispatch.'}
    if native_route:row['native_route']=native_route
    save(destination,row)
    return row


def record_search_end(out):
    out=Path(out);origin=read_bound(binding(out/'SEARCH-CPU-ORIGIN.json'))
    identity=read_bound(binding(out/'BATCH-IDENTITY.json'))
    if identity!=origin['aggregate']:raise ValueError('The search aggregate changed.')
    sample=sample_aggregate(job_aggregate(identity,out))
    if sample['CPU_seconds']<origin['CPU_seconds']:raise ValueError('The search CPU counter decreased.')
    save(out/'SEARCH-CPU-END.json',{'aggregate':identity,'CPU_seconds':sample['CPU_seconds'],
        'search_CPU_seconds':sample['CPU_seconds']-origin['CPU_seconds'],
        'scope':'Exact owned aggregate immediately after the native RPC returned.'})


def search_accounting(out,identity,cpu_seconds):
    out=Path(out);path=out/'SEARCH-CPU-ORIGIN.json'
    if not path.exists():return {'search_started':False,'setup_CPU_seconds':cpu_seconds,
        'search_CPU_seconds':None,'origin_cpu':None,'end_cpu':None,'search_active':False}
    origin=read_bound(binding(path))
    if origin['aggregate']!=identity:raise ValueError('The origin names another aggregate.')
    from native_route import authority_body
    expected_body=authority_body(origin['native_route']) if origin.get('native_route') else 'zesu_block.'
    if origin['tool']!='rocq_check' or origin['arguments'].get('body')!=expected_body:
        raise ValueError('The origin names another native command.')
    start=origin['CPU_seconds'];end_path=out/'SEARCH-CPU-END.json';end=None
    if end_path.exists():
        ended=read_bound(binding(end_path))
        if ended['aggregate']!=identity:raise ValueError('The search end names another aggregate.')
        end=ended['CPU_seconds']
    if cpu_seconds<start or end is not None and end<start:raise ValueError('The search CPU counter decreased.')
    return {'search_started':True,'setup_CPU_seconds':start,
        'search_CPU_seconds':max(0,(end if end is not None else cpu_seconds)-start),
        'post_search_CPU_seconds':max(0,cpu_seconds-end) if end is not None else None,
        'origin_cpu':start,'end_cpu':end,'origin':binding(path),
        'search_active':end is None and not any((out/'native'/name).exists()
            for name in ['WORKER-FAILURE.json','INFRASTRUCTURE-FAILURE.json'])}


def append_growth(out,row):
    with (Path(out)/'MEMORY-GROWTH.jsonl').open('a') as stream:
        stream.write(json.dumps(row,sort_keys=True)+'\n')
        stream.flush()


def capture_before_stop(out):
    """Retain the complete last available state before stopping the aggregate.

    A pending PET call has no returned internal state. Never label its
    pre-call export as the state at the CPU boundary.
    """
    from entry_pilot_checker import complete_groups
    out=Path(out);path=out/'native/LAST-COMPLETED-STATE.json'
    if not path.exists():path=out/'native/PRE-CALL-STATE.json'
    report={'schema':'scratch.before-stop-state.v1',
            'current_internal_state':None,'current_internal_group_counts':None,
            'state_source':'unavailable','group_counts':None,'residual':None}
    if path.exists():
        try:
            before=read_bound(binding(path));export=before['export']
            groups=complete_groups(export)
            state=read_bound(export)
            destination=out/'STOP-RETAINED-STATE.json';save(destination,state)
            report.update(state_source=before['state_source'],residual=binding(destination),
                group_counts={'active':len(groups['goals']),
                              'focus_frames':len(groups['stack']),
                              'frame_goals':sum(len(left)+len(right) for left,right in groups['stack']),
                              'shelves':len(groups['shelf']),'given_up':len(groups['given_up'])})
        except (OSError,KeyError,ValueError,TypeError) as error:
            report['unavailable_reason']=str(error)
    else:report['unavailable_reason']='No complete pre-call export exists.'
    report['qualification']='The retained export is the latest completed checkpoint. In-flight progress and internal stopping counts remain unknown.'
    save(out/'BEFORE-STOP-STATE.json',report)
    return report

def finish_growth(out,count,started,last,returncode,*,family=False,claim_bytes=None,family_threshold_bytes=16*1024**3,memory_job=None,instruction_checkpoints=None):
    final=Path(out)/'CPU-FINAL.json'
    accounting=read_bound(binding(final)) if final.exists() else None
    identity=read_bound(binding(Path(out)/'BATCH-IDENTITY.json')) if (Path(out)/'BATCH-IDENTITY.json').exists() else None
    if family and accounting is not None and claim_report_required(accounting.get('memory_current_bytes') or 0,claim_bytes,family=True,peak_bytes=accounting.get('aggregate_peak_bytes'),family_threshold_bytes=family_threshold_bytes) and not (Path(out)/'MEMORY-CLAIM-REPORT.json').exists():
        save(Path(out)/'MEMORY-CLAIM-REPORT.json',{'report_only':True,'CPU_seconds':accounting.get('cpu_seconds'),'memory_current_bytes':accounting.get('memory_current_bytes'),'memory_peak_bytes':accounting.get('aggregate_peak_bytes'),'claim_bytes':claim_bytes,'family_peak_threshold_bytes':family_threshold_bytes,'reason':'family_peak_above_'+str(family_threshold_bytes//1024**3)+'GiB','accounting_source':'final_accounting','proof_search_stopped':False})
    costs=search_accounting(out,identity,accounting['cpu_seconds']) if accounting is not None and identity is not None else None
    from port_native_policy import cpu_budgets
    search_budget,setup_budget=cpu_budgets(memory_job,CPU_STOP_SECONDS,SETUP_CPU_STOP_SECONDS)
    if costs is not None:
        costs['search_active']=False
        if instruction_checkpoints is not None:
            instruction_checkpoints.sample({**costs,'CPU_seconds':accounting['cpu_seconds']})
    save(Path(out)/'MEMORY-GROWTH.json',{'schema':'scratch.memory-versus-cpu.v1',
        'search_accounting':costs,'search_budget_CPU_seconds':search_budget,
        'setup_budget_CPU_seconds':setup_budget,'prerequisites_excluded_from_search':True,
        'period_seconds':.5,'period_is_best_effort':True,'sample_count':count,
        'samples':binding(Path(out)/'MEMORY-GROWTH.jsonl') if count else None,
        'elapsed_monotonic_seconds':time.monotonic()-started,'last_sample':last,
        'final_accounting':binding(final) if accounting is not None else None,
        'final_accounting_available':accounting is not None,
        'final_memory_accounting_available':bool(accounting and accounting.get('final_memory_accounting_available')),
        'returncode':returncode,'custom_observer':False,
        'scope':'Exact owned aggregate. The existing external-limit loop records the samples.',
        'limit':'A last sample is not final accounting. Missing cleanup-time data remains unavailable.'})
    return returncode

def wait_with_limits(child,out,claim_bytes,prior_cpu_seconds=0,*,phase='native',memory_job=None,family=False,family_threshold_bytes=16*1024**3):
    policy=_MonitorPolicy(memory_job,phase)
    token=_MONITOR_POLICY.set(policy)
    try:
        return _wait_with_limits(child,out,claim_bytes,prior_cpu_seconds,phase=phase,
            memory_job=memory_job,family=family,family_threshold_bytes=family_threshold_bytes)
    finally:
        _MONITOR_POLICY.reset(token)


def _wait_with_limits(child,out,claim_bytes,prior_cpu_seconds=0,*,phase='native',memory_job=None,family=False,family_threshold_bytes=16*1024**3):
    physical=_policy(memory_job,phase).physical
    out=Path(out);started=time.monotonic();count=0;last=None
    from port_native_policy import port_case
    instruction_checkpoints=None
    if port_case(memory_job) is not None:
        from instruction_checkpoints import Observer
        instruction_checkpoints=Observer(out,memory_job)
    while child.poll() is None:
        marker=out/'BATCH-IDENTITY.json'
        if marker.exists():
            identity=read_bound(binding(marker))
            try:
                group=exact_aggregate(identity,physical,memory_job=memory_job)
                sample=sample_aggregate(group)
            except FileNotFoundError:
                time.sleep(.5);continue
            cpu=sample['CPU_seconds'];memory=sample['memory_current_bytes'];peak=sample['memory_peak_bytes']
            search=search_accounting(out,identity,cpu)
            reason=stop_reason(cpu,memory,claim_bytes,prior_cpu_seconds,phase=phase,
                origin_cpu=search['origin_cpu'],end_cpu=search['end_cpu'],memory_job=memory_job)
            last={'schema':'scratch.memory-versus-cpu.sample.v1','sequence':count,
                'elapsed_monotonic_seconds':time.monotonic()-started,
                'prior_CPU_seconds':prior_cpu_seconds,'total_CPU_seconds':cpu+prior_cpu_seconds,
                'aggregate':identity,'stop_reason':reason,'phase':phase,**search,**sample}
            last['search_active']=bool(search.get('search_active')) and reason is None
            append_growth(out,last);count+=1
            if instruction_checkpoints is not None:instruction_checkpoints.sample(last)
            if claim_report_required(memory,claim_bytes,family=family,peak_bytes=peak,family_threshold_bytes=family_threshold_bytes) and not (out/'MEMORY-CLAIM-REPORT.json').exists():
                exact_aggregate(identity,physical,memory_job=memory_job)
                save(out/'MEMORY-CLAIM-REPORT.json',{'report_only':True,'CPU_seconds':cpu,'memory_current_bytes':memory,'memory_peak_bytes':peak,'claim_bytes':claim_bytes,'report_multiplier':None if family else CLAIM_REPORT_MULTIPLIER,'family_peak_threshold_bytes':family_threshold_bytes if family else None,'reason':'family_peak_above_'+str(family_threshold_bytes//1024**3)+'GiB' if family else 'peak_above_twice_claim','physical_memory_fence_bytes':physical,'aggregate':identity,'proof_search_stopped':False})
            if reason:
                exact_aggregate(identity,physical,memory_job=memory_job)
                checkpoint=capture_before_stop(out)
                save(out/'EXTERNAL-STOP.json',{'last_completed_checkpoint':binding(out/'BEFORE-STOP-STATE.json'),'inflight_progress':'unknown','reason':reason,'CPU_seconds':cpu,'prior_CPU_seconds':prior_cpu_seconds,'memory_current_bytes':memory,'memory_peak_bytes':peak,'memory_events':sample['memory_events'],'claim_bytes':claim_bytes,'aggregate':identity,'no_tactic_timeout':True,'phase':phase,**search})
                save(out/'CPU-FINAL.json',{'cpu_seconds':cpu,'raw_cpu_stat':sample['raw_cpu_stat'],'aggregate_peak_bytes':peak,'aggregate_peak_KiB':(peak+1023)//1024,'memory_current_bytes':memory,'memory_events':sample['memory_events'],'final_memory_accounting_available':True,'scope':'Exact owned aggregate immediately before the external stop.','CPU_budget_enforced':True,'CPU_budget_scope':'native_search' if reason=='external_CPU_stop' else 'setup_or_prerequisites','phase':phase,**search,'custom_observer':False})
                reply=subprocess.run(['/usr/bin/systemctl','--user','stop',group.name],capture_output=True,text=True)
                save(out/'EXTERNAL-STOP-REPLY.json',{'returncode':reply.returncode,'stdout':reply.stdout,'stderr':reply.stderr})
                if reply.returncode:raise RuntimeError('The exact scratch aggregate did not stop.')
                return finish_growth(out,count,started,last,child.wait(),family=family,claim_bytes=claim_bytes,family_threshold_bytes=family_threshold_bytes,memory_job=memory_job,instruction_checkpoints=instruction_checkpoints)
        time.sleep(.5)
    return finish_growth(out,count,started,last,child.wait(),family=family,claim_bytes=claim_bytes,family_threshold_bytes=family_threshold_bytes,memory_job=memory_job,instruction_checkpoints=instruction_checkpoints)
