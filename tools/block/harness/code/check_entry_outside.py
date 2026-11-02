import sys,os
sys.dont_write_bytecode=True
os.environ['PYTHONDONTWRITEBYTECODE']='1'
import clone_copy
#!/usr/bin/env python3
"""Check one entry from an outside caller. Keep all other entry bodies private."""
import argparse
from copy import deepcopy
import fcntl
import json
import os
from pathlib import Path
import re
import signal
import subprocess
import sys
import time
import traceback
import uuid

from module_memory import measurement_claim
from admission_memory import guard_lock, check_test_ledger

from check_entry import (ROOT,answer_error_feedback,atomic_json,attempt_identity,bound_rows,digest,require_truth_gate)
from entry_pilot_checker import bound_json,complete_groups,native_result,strict_loads,validate_inline

CONFIG=ROOT/'_build/check-entry-release/CONFIG.json'
HEADS={'FindRegMapsTo','FindMemMapsTo','FindInstrKind','WPasm','SHELVED_SIDECOND',
       'envs_entails','bi_emp_valid','eq','False','True'}
PUBLIC_LIMIT=6144


def ticks(pid):
    text=Path(f'/proc/{pid}/stat').read_text()
    return int(text[text.rfind(')')+2:].split()[19])


def identity_alive(pid,startticks):
    try:return ticks(pid)==startticks
    except FileNotFoundError:return False


def validate_complete_gate(gate,runtime,selected_case=None):
    if gate.get('proof_provider_sha256')!=digest(runtime['proof_provider']):
        raise ValueError('The native gate covers another proof provider.')
    cases={row['case']['case_id']:row for row in runtime['cases']}
    require_truth_gate(gate,cases,selected_case)
    rows=gate.get('truth_controls',{})
    if set(rows)!=set(gate['passed_case_ids']):
        raise ValueError('The gate lacks the released native truth acceptances.')
    for case_id,binding in rows.items():
        value=bound_json(binding['result']['path'],binding['result']['sha256'])
        accepted=bound_json(binding['Root_acceptance']['path'],binding['Root_acceptance']['sha256'])
        row=cases[case_id]
        if (accepted.get('accepted') is not True
                or accepted.get('result_sha256')!=binding['result']['sha256']
                or value.get('case_id')!=case_id or value.get('primary_success') is not True
                or value.get('source_commit')!=runtime['source_commit']
                or value.get('response_sha256')!=row['truth_control_response']['sha256']):
            raise ValueError('A native truth control lacks exact Root acceptance.')
        response=bound_json(row['truth_control_response']['path'],row['truth_control_response']['sha256'])
        if value.get('identity')!=attempt_identity(row,response):
            raise ValueError('A truth receipt changed its candidate or edge identity.')
        expected={side:row[side]['statement_sha256'] for side in ('predecessor','successor')}
        if not native_result(value['native_receipts'],expected):
            raise ValueError('A truth result lacks both exact native proofs.')
        for side,receipt in value['native_receipts'].items():
            if receipt.get('statement')!=row[side]['statement']:
                raise ValueError('A truth receipt changed its literal statement.')


def canonical_functions(policy):
    sys.path.insert(0,policy['reviewed_helpers'])
    from claims import active_claims
    from io_helpers import memory_available
    return active_claims,memory_available


def reserve(policy,key,owner,receipt,*,available=None,claims_fn=None,pause=time.sleep,recheck=lambda:None):
    from memory_policy import admission_claim
    from admission_memory import projection, guard_lock
    policy['minimum_claim_bytes'] = admission_claim(policy)
    actual_claims,actual_available=canonical_functions(policy)
    claims_fn=actual_claims if claims_fn is None else claims_fn
    available=actual_available if available is None else available
    records=[]
    while True:
        recheck()
        check_test_ledger(policy['ledger'])
        with guard_lock(), Path(policy['lock']).open('a') as handle:
            fcntl.flock(handle,fcntl.LOCK_EX)
            data=strict_loads(Path(policy['ledger']).read_text())
            if data['fixed_claims'].get(key,0):raise ValueError('The unique attempt claim already exists.')
            claims=claims_fn(data,policy['legacy_release_bindings']);free=available()
            sizing=projection(data,claims,policy['minimum_claim_bytes']+policy['capture_headroom_bytes'],free)
            total=sizing['requested_total_bytes']
            record={'time_ns':time.time_ns(),'claim_key':key,'owner':owner,
                'claim_bytes':policy['minimum_claim_bytes'],'active_claim_bytes':sum(claims.values()),
                'capture_headroom_bytes':policy['capture_headroom_bytes'],'MemAvailable_bytes':free,
                'budget_bytes':free*7//10,'requested_total_bytes':total,**sizing}
            if record['admitted']:
                data['fixed_claims'][key]=policy['minimum_claim_bytes']
                data.setdefault('entry_pilot_outside_owners',{})[key]=owner
                data.setdefault('claim_fences',{})[key]={'owner':owner,'physical_fence_bytes':policy['physical_fence_bytes']}
                if policy.get('output_path'):
                    data.setdefault('claim_locations',{})[key]={'owner':owner,'kind':'entry','output_path':policy['output_path']}
                atomic_json(policy['ledger'],data)
            record['ledger_sha256']=digest(policy['ledger'])
            records.append(record);atomic_json(receipt,records)
        if record['admitted']:return record
        pause(60)


def closed_aggregate(identity,batch_pid,batch_ticks):
    if identity_alive(batch_pid,batch_ticks):return False
    group=Path(identity['aggregate_path'])
    try:info=group.stat()
    except FileNotFoundError:return True
    if (info.st_dev,info.st_ino)!=(identity['aggregate_device'],identity['aggregate_inode']):
        raise ValueError('The owned aggregate identity changed.')
    events=dict(line.split() for line in (group/'cgroup.events').read_text().splitlines())
    if events.get('populated') not in ('0','1'):raise ValueError('The aggregate population record is invalid.')
    return events['populated']=='0'


def release(policy,key,owner,closure_binding,*,ledger=None):
    path=Path(ledger or policy['ledger'])
    closure=bound_json(closure_binding['path'],closure_binding['sha256'])
    if closure.get('all_owned_actors_closed') is not True or closure.get('owner')!=owner:
        raise ValueError('The claim lacks its exact closure receipt.')
    check_test_ledger(path)
    with guard_lock(), Path(policy['lock']).open('a') as handle:
        fcntl.flock(handle,fcntl.LOCK_EX)
        data=strict_loads(path.read_text())
        if data.get('entry_pilot_outside_owners',{}).get(key)!=owner:
            raise ValueError('The canonical claim owner changed.')
        amount=data['fixed_claims'].get(key,0)
        if type(amount) is not int or amount<policy['minimum_claim_bytes']:
            raise ValueError('The attempt claim is absent or invalid.')
        data['fixed_claims'][key]=0
        data.setdefault('entry_pilot_outside_releases',{})[key]={
            'bytes':amount,'closure':closure_binding,'owner':owner,'time_ns':time.time_ns()}
        atomic_json(path,data)
        return {'claim_key':key,'bytes':amount,'released':True,'ledger_sha256':digest(path)}


def compact_residual(result):
    retained=result.get('retained_goal_state')
    if retained is None:return None,None
    value=bound_json(retained['path'],retained['sha256'])
    groups=value['kernel_groups']
    heads=[]
    goals=list(groups['goals'])+list(groups['shelf'])+list(groups['given_up'])
    goals += [goal for left,right in groups['stack'] for goal in left+right]
    for goal in goals:
        match=re.match(r'^\s*\(*\s*@?([A-Za-z_][A-Za-z0-9_.]*)',goal['ty'])
        head=match.group(1).split('.')[-1] if match else None
        if head in HEADS and head not in heads:heads.append(head)
    side=result.get('last_progress',{}).get('side')
    summary={'failed_proof_side':side if side in ('predecessor','successor') else 'setup',
        'active_goals':len(groups['goals']),'focus_frames':len(groups['stack']),
        'focused_frame_goals':sum(len(left)+len(right) for left,right in groups['stack']),
        'shelved_goals':len(groups['shelf']),'given_up_goals':len(groups['given_up']),
        'goal_constructors':heads,'state_source':retained.get('state_source','unspecified')}
    return summary,{'path':retained['path'],'sha256':retained['sha256'],'private':True}


def safe_case_id(value):
    return value if re.fullmatch(r'DI-800d[0-9a-f]{4}',value) else None


def retained_result(output):
    result_path=Path(output)/'RESULT.json'
    result=strict_loads(result_path.read_text()) if result_path.exists() else {}
    if result.get('native_route'):raise ValueError('The stock outside checker is not released for a minimal native route.')
    actual=result.get('first_residual')
    residual_path=Path(actual['path']) if isinstance(actual,dict) else Path(output)/'first-residual/RESIDUAL.json'
    if residual_path.exists():
        index_path=residual_path.parent/'PRIVATE-INDEX.json'
        index=strict_loads(index_path.read_text())
        expected=actual['sha256'] if isinstance(actual,dict) else index.get('retained',{}).get('sha256')
        if expected is None or digest(residual_path)!=expected:
            raise ValueError('The complete retained residual hash changed.')
        export={'success':True,'path':str(residual_path),'sha256':expected}
        complete_groups(export)
        result['retained_goal_state']={'path':str(residual_path),'sha256':expected,
            'state_source':index['state_source'],'qualifier':index['qualifier'],'agent_visible':False}
    index_path=Path(output)/'PRE-CALL-STATE.json'
    completed_success = (result.get('primary_success') is True
                         and result.get('last_progress', {}).get('phase') == 'complete')
    if not completed_success and result.get('retained_goal_state') is None and index_path.exists():
        index=strict_loads(index_path.read_text())
        if (index.get('state_source')!='retained_pre_call_state'
                or index.get('requested_body')!='zesu_block.'
                or index.get('side')!=result.get('last_progress',{}).get('side')):
            raise ValueError('The retained pre-call record has another request or proof side.')
        complete_groups(index['export'])
        result['retained_goal_state']={'path':index['export']['path'],'sha256':index['export']['sha256'],
            'state_source':'retained_pre_call_state',
            'qualifier':'Complete retained pre-call state. The internal stopping state is unavailable.',
            'agent_visible':False}
    return result


def public_result(case_id,result,released):
    summary,pointer=compact_residual(result)
    success=result.get('primary_success') is True and released and result.get('stock_batch_exit')==0
    allowed={'both_exact_native_proofs_pass','native_proof_failed','aggregate_cpu_budget','checker_error','answer_refused'}
    reason=result.get('reason','checker_error')
    if reason not in allowed:reason='checker_error'
    if result.get('primary_success') is True and result.get('stock_batch_exit')!=0:
        reason='stock_batch_failed'
    if not released:reason='closure_incomplete_claim_retained'
    value={'schema':'entry-pilot.outside-result.v1','case_id':safe_case_id(case_id),'status':'pass' if success else 'fail',
        'primary_success':success,'reason':reason,'residual':summary,'full_private_residual':pointer,
        'cpu_seconds':result.get('cpu',{}).get('cpu_seconds'),'cpu_budget_seconds':result.get('cpu_budget_seconds'),
        'claim_released':released,'separate_equivalence_proof':False}
    if reason == 'answer_refused':
        value['answer_error'] = answer_error_feedback(result.get('answer_error', ''))
    if len(json.dumps(value,ensure_ascii=False).encode())>PUBLIC_LIMIT:raise ValueError('The compact feedback exceeds six KiB.')
    return value


def clean_environment():
    env={key:value for key,value in os.environ.items() if not key.startswith(('ZESU_','ROCQ_','COQC_'))
         and key not in ('COQPATH','COQBIN','COQC','OCAMLPATH')}
    env.update(PATH='/home/cody/islaris/_opam/bin:/usr/local/bin:/usr/bin:/bin',
        OPAM_SWITCH_PREFIX='/home/cody/islaris/_opam')
    return env


def snapshot_configuration(config,private,expected):
    raw=CONFIG.read_bytes()
    if digest(CONFIG)!=expected or strict_loads(raw.decode())!=config:
        raise ValueError('The outside configuration changed before its snapshot.')
    snapshot=Path(private)/'CONFIG.json'
    clone_copy.copy2(CONFIG,snapshot)
    if digest(snapshot)!=expected:
        raise ValueError('The immutable configuration snapshot changed.')
    return {'path':str(snapshot),'sha256':expected}


def run(args,config,config_digest):
    raise ValueError("The legacy outside launcher is held pending aggregate-policy integration.")
    runtime=bound_json(config['runtime']['path'],config['runtime']['sha256'])
    bound_rows(runtime['bindings'])
    if not config.get('execution_released'):raise ValueError('The outside wrapper lacks Root release.')
    if runtime.get('outside_provider_pending') is not False:
        raise ValueError('The corrected proof provider remains held.')
    gate=bound_json(config['truth_gate']['path'],config['truth_gate']['sha256'])
    validate_complete_gate(gate,runtime,args.case_id)
    response=strict_loads(args.answer.read_text())
    row=next((row for row in runtime['cases'] if row['case']['case_id']==args.case_id),None)
    if row is None:raise ValueError('The requested case is outside the nineteen eligible entries.')
    validate_inline(response,row['case'])
    token=uuid.uuid4().hex
    private=ROOT/'_build/check-entry-outside-attempts'/token
    private.mkdir(parents=True,mode=0o700)
    config_binding=snapshot_configuration(config,private,config_digest)
    source=private/'ANSWER.json';clone_copy.copy2(args.answer,source);source.chmod(0o600)
    if strict_loads(source.read_text())!=response:raise ValueError('The answer changed during its copy.')
    output=private/'native'
    runtime=deepcopy(runtime);runtime['mode']='candidate';runtime['truth_gate']=config['truth_gate']
    runtime['execution_released']=True
    policy=runtime['canonical_admission'];key='EntryPilotOutside_v1_'+token
    policy.update(claim_key=key,case_id=args.case_id,response_sha256=digest(source),output_path=str(output))
    owner={'token':token,'pid':os.getpid(),'startticks':ticks(os.getpid()),'case_id':args.case_id,'answer_sha256':digest(source)}
    runtime['bindings'].append(config_binding)
    runtime['bindings'].append(config['truth_gate'])
    runtime_path=private/'RUNTIME.json';atomic_json(runtime_path,runtime)
    reserved=False;child=None;batch_ticks=None;result={};released=False
    def interrupted(_number,_frame):raise KeyboardInterrupt('The outside caller stopped the attempt.')
    handlers={sig:signal.signal(sig,interrupted) for sig in (signal.SIGTERM,signal.SIGINT,signal.SIGHUP)}
    try:
        reserve(policy,key,owner,private/'ADMISSION.json',recheck=lambda:bound_rows(runtime['bindings']));reserved=True
        bound_rows(runtime['bindings'])
        argv=[str(ROOT/'tools/resource_guard.sh'),'batch','entry-pilot-outside','--',runtime['python'],
            str(ROOT/'tools/block/entry_attempt_inner.py'),str(private),runtime['python'],
            str(ROOT/'tools/block/check_entry.py'),str(source),'--runtime',str(runtime_path),
            '--runtime-sha256',digest(runtime_path),'--output',str(output),'--execute']
        atomic_json(private/'LAUNCH.json',{'argv':argv,'owner':owner})
        with (private/'stock.stdout').open('wb') as stdout,(private/'stock.stderr').open('wb') as stderr:
            child=subprocess.Popen(argv,cwd=ROOT,env=dict(clean_environment(), CHECK_ENTRY_MODULE_ORIGINS=str(private/'MODULE-ORIGINS.json')),stdout=stdout,stderr=stderr,start_new_session=True)
            batch_ticks=ticks(child.pid)
            atomic_json(private/'BATCH-PROCESS.json',{'pid':child.pid,'startticks':batch_ticks})
            code=child.wait()
        result=retained_result(output)
        atomic_json(private/'ADAPTED-RESULT.json',result)
        result['stock_batch_exit']=code
    except BaseException:
        atomic_json(private/'WRAPPER-FAILURE.json',{'private_error':traceback.format_exc()})
        if child is not None and child.poll() is None:
            os.killpg(child.pid,signal.SIGTERM)
            try:child.wait(timeout=30)
            except subprocess.TimeoutExpired:
                # A failed stock cleanup cannot justify releasing its claim.
                os.killpg(child.pid,signal.SIGKILL);child.wait()
    finally:
        for sig,handler in handlers.items():signal.signal(sig,handler)
        try:
            identity_file=private/'BATCH-IDENTITY.json'
            closed=False;identity=None
            if reserved and child is None:
                # No launch occurred. There is no owned batch or proof actor.
                closed=True
            elif reserved and child is not None and batch_ticks is not None and identity_file.exists():
                identity=strict_loads(identity_file.read_text())
                closed=closed_aggregate(identity,child.pid,batch_ticks)
            if reserved:
                closure={'owner':owner,'claim_key':key,'all_owned_actors_closed':closed,
                    'batch_pid':child.pid if child is not None else None,'batch_startticks':batch_ticks,
                    'batch_exit':child.returncode if child is not None else None,
                    'aggregate_identity':identity,'no_launch_occurred':child is None,'time_ns':time.time_ns()}
                atomic_json(private/'CLOSURE.json',closure)
                if closed:
                    record=release(policy,key,owner,{'path':str(private/'CLOSURE.json'),'sha256':digest(private/'CLOSURE.json')})
                    atomic_json(private/'RELEASE.json',record);released=True
        except BaseException:
            atomic_json(private/'CLOSURE-FAILURE.json',{'private_error':traceback.format_exc(),'claim_retained':True})
        public=public_result(args.case_id,result,released)
        public['private_result']={'path':str(output/'RESULT.json'),'private':True}
        if len(json.dumps(public,ensure_ascii=False).encode())>PUBLIC_LIMIT:
            raise ValueError('The final public feedback exceeds six KiB.')
        atomic_json(args.output/'RESULT.json',public)
        print(json.dumps(public,ensure_ascii=False))
    return 0 if public['primary_success'] else 1


def validate_output(path, *, base=Path('/home/cody/zesislar'), root=ROOT):
    resolved=Path(path).resolve()
    base=Path(base).resolve();root=Path(root).resolve()
    private_roots=[base/'_build',root/'_build']
    if resolved.is_relative_to(base) and not any(resolved.is_relative_to(p) for p in private_roots):
        raise ValueError('The output directory must not belong to a source tree.')
    return resolved


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('case_id');parser.add_argument('answer',type=Path);parser.add_argument('output',type=Path)
    args=parser.parse_args();os.umask(0o077)
    try:
        args.output=validate_output(args.output)
        args.output.mkdir(parents=True,exist_ok=False,mode=0o700)
    except (ValueError,OSError):
        print(json.dumps({'schema':'entry-pilot.outside-result.v1','case_id':safe_case_id(args.case_id),
            'status':'fail','primary_success':False,'reason':'output_path_refused'}))
        return 2
    try:
        expected=CONFIG.with_suffix('.sha256').read_text().strip()
        config=bound_json(CONFIG,expected)
        return run(args,config,expected)
    except BaseException:
        if not (args.output/'RESULT.json').exists():
            public={'schema':'entry-pilot.outside-result.v1','case_id':safe_case_id(args.case_id),'status':'fail',
                'primary_success':False,'reason':'setup_or_closure_error','residual':None,
                'full_private_residual':None,'claim_released':False,'separate_equivalence_proof':False}
            atomic_json(args.output/'RESULT.json',public);print(json.dumps(public))
        return 1

if __name__=='__main__':raise SystemExit(main())
