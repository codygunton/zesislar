import sys,os
sys.dont_write_bytecode=True
os.environ['PYTHONDONTWRITEBYTECODE']='1'
"""Dispatch independent chain blocks with fresh canonical memory admission."""
from copy import deepcopy
import clone_copy
import fcntl
import os
from pathlib import Path
import subprocess
import sys
import time

sys.path[1:1] = [str(Path(__file__).resolve().parents[2]), str(Path(__file__).resolve().parents[3])]

from entry_chain import binding,check_bindings,digest,read_bound,save,strict_loads
from entry_chain_run import ready_claim_priority
from entry_chain_resources import normalize_cpu,publish_latch
from check_entry_outside import canonical_functions,identity_alive
from admission_memory import projection, guard_lock

ROOT=Path(__file__).resolve().parents[4]


def safe_width(policy,jobs,*,available=None,claims_fn=None):
    actual_claims,actual_available=canonical_functions(policy)
    available=actual_available if available is None else available
    claims_fn=actual_claims if claims_fn is None else claims_fn
    with guard_lock(), Path(policy['lock']).open('a') as lock:
        fcntl.flock(lock,fcntl.LOCK_EX)
        data=strict_loads(Path(policy['ledger']).read_text())
        active=claims_fn(data,policy['legacy_release_bindings']);free=available()
        largest=max(job['claim_bytes'] for job in jobs)
        sizing=projection(data,active,0,free)
        room=sizing['available_new_claim_bytes']
        width=max(0,min(48,len(jobs),room//largest))
        return {'safe_new_workers':width,'largest_reviewed_initial_claim_bytes':largest,
                'active_claims':active,'active_claim_bytes':sum(active.values()),
                'MemAvailable_bytes':free,'budget_bytes':free*7//10,'time_ns':time.time_ns(),**sizing}


def submit(config_path,config,key,output):
    watcher=config['watcher']
    if digest(watcher['path'])!=watcher['sha256']:
        raise ValueError('The bound watcher executable changed.')
    controller=config['job_controller']
    check_bindings([controller,config['result_adapter']])
    argv=[sys.executable,'-B',watcher['path'],'watch','--label','infra-a-h1-chain-'+key,'--',
          sys.executable,'-B',controller['path'],
          str(config_path),digest(config_path),key,str(output)]
    result=subprocess.run(argv,cwd=ROOT,capture_output=True,text=True)
    save(Path(config['scheduler_output'])/('WATCH-'+key+'.json'),
         {'argv':argv,'returncode':result.returncode,'stdout':result.stdout,'stderr':result.stderr})
    if result.returncode:
        publish_latch(config['shared_latch'],'watcher-submission-failed',{'key':key,'stderr':result.stderr})
        raise RuntimeError('The all-exit watcher did not start.')


def await_result(output):
    while not (Path(output)/'RESULT.json').exists():time.sleep(1)
    return strict_loads((Path(output)/'RESULT.json').read_text())


def require_shared_health(result):
    if result.get('shared_infrastructure_failure') or result.get('observer_failure'):
        raise RuntimeError('A shared infrastructure or resource failure holds later dispatch.')


def prerequisite_readiness(config,result):
    out=Path(config['jobs'][0]['output']);native=out/'native'
    if result.get('success') is not True:
        raise RuntimeError('Shared prerequisite compilation failed.')
    records=[]
    workspace=out/'workspace'
    sealed_owned=False
    if config.get('seed_binding_reference'):
        from seed_bindings import descriptor,validate
        reference=config['seed_binding_reference']
        if descriptor(reference['descriptor']).get('sealed_boundary'):
            staged=read_bound(binding(out/'RUNTIME.json'))
            workspace=Path(config['prepared_workspace'])
            if (staged.get('prepared_workspace')!=str(workspace) or
                    staged.get('seed_binding_reference',{}).get('descriptor')!=reference['descriptor']):
                raise ValueError('The completed prerequisite names another sealed workspace.')
            validate(staged['seed_binding_reference'],workspace)
            if (read_bound(binding(out/'RESULT.json'))!=result or
                    not read_bound(binding(out/'CLOSURE.json'))['all_owned_actors_closed'] or
                    not read_bound(binding(out/'RELEASE.json'))['released']):
                raise ValueError('The sealed prerequisite has not closed and released.')
            sealed_owned=True
    for module in config['jobs'][0]['ordered_modules']:
        receipt_path=native/('dependency-'+module+'.json')
        receipt=strict_loads(receipt_path.read_text())
        if not receipt['result'].get('success'):
            raise ValueError('A prerequisite lacks its successful MCP receipt.')
        source=Path(receipt['source']);obj=Path(receipt['object'])
        if digest(source)!=receipt['source_sha256'] or digest(obj)!=receipt['object_sha256']:
            raise ValueError('A prerequisite source or object changed.')
        if sealed_owned:
            expected=workspace/config['proof_runtime']['module_files'][module]
            if source.resolve()!=expected.resolve() or obj.resolve()!=expected.with_suffix('.vo').resolve():
                raise ValueError('The sealed prerequisite source/object differs from its logical module.')
        # Ordinary jobs copy from their owned workspace. A sealed job already wrote
        # these exact artifacts into its owned prefix and must not copy them again.
        target=Path(config['prepared_workspace'])/relative_to_owned(source,workspace)
        for suffix in ['.vo','.glob','.vos','.vok']:
            old=source.with_suffix(suffix);new=target.with_suffix(suffix)
            if old.is_file():
                import shutil
                if sealed_owned:
                    if old.resolve()!=new.resolve():
                        raise ValueError('A sealed prerequisite artifact leaves its owned prefix.')
                else:
                    clone_copy.copy2(old,new)
                    if digest(old)!=digest(new) or old.stat().st_ino==new.stat().st_ino:
                        raise ValueError('A shared prerequisite copy differs.')
                records.append(binding(new))
    readiness={'schema':'entry-chain.prerequisite-readiness.v1','objects':records,
               'prerequisite_result':binding(out/'RESULT.json'),'all_required_compiles_passed':True,
               'owned_sealed_artifacts_retained':sealed_owned}
    save(config['readiness']['path'],readiness)
    return readiness


def relative_to_owned(path,root):
    path,root=Path(path).resolve(),Path(root).resolve()
    if not path.is_relative_to(root):raise ValueError('A prerequisite leaves its owned job.')
    return path.relative_to(root)


def main():
    normalize_cpu()
    config_path,expected=Path(sys.argv[1]),sys.argv[2]
    config=read_bound({'path':str(config_path),'sha256':expected})
    check_bindings(config['bindings'])
    if not config.get('execution_released'):raise ValueError('The chain scheduler remains held.')
    scheduler=Path(config['scheduler_output']);scheduler.mkdir(parents=True,exist_ok=False)
    ready_claim_priority(config,config['priority_receipt'])
    # Shared imports compile once. The representative is one of the required block rows.
    pre=config['jobs'][0]
    submit(config_path,config,pre['key'],pre['output'])
    prerequisite_readiness(config,await_result(pre['output']))
    # Freeze a post-prerequisite config. The original source runtime stays immutable.
    current=deepcopy(config)
    current['readiness']=binding(config['readiness']['path'])
    current_path=scheduler/'READY-RUNTIME.json';save(current_path,current)
    pilot=current['jobs'][1]
    submit(current_path,current,pilot['key'],pilot['output'])
    pilot_result=await_result(pilot['output'])
    require_shared_health(pilot_result)
    # A native-open pilot is a block result. Its healthy resource observation sizes later jobs.
    # The new aggregate peak can only increase the measured memory floor.
    floor=(int(pilot_result['aggregate_peak_KiB'])*1024*3+1)//2
    for job in current['jobs'][2:]:job['claim_bytes']=max(job['claim_bytes'],floor)
    current_path=scheduler/'BROAD-RUNTIME.json';save(current_path,current)
    pending=list(current['jobs'][2:]);active=[];completed=[pilot_result];sample=0
    while pending or active:
        if Path(current['shared_latch']).exists():
            raise RuntimeError('A shared observer or growth failure stopped new dispatch.')
        for job in list(active):
            result=Path(job['output'])/'RESULT.json'
            if result.exists():
                completed.append(strict_loads(result.read_text()));active.remove(job)
        if pending:
            sizing=safe_width(current['admission'],pending)
            save(scheduler/('SIZING-%06d.json'%sample),sizing);sample+=1
            # Reserve enough capacity for the largest reviewed task. Actual reservations stay per job.
            eligible=[job for job in pending if job['claim_bytes']<=sizing['available_new_claim_bytes']]
            if eligible and len(active)<48:
                job=eligible[0];pending.remove(job);submit(current_path,current,job['key'],job['output']);active.append(job)
                # Wait for admission and its first monitor observation before another launch.
                while not (Path(job['output'])/'growth/STATUS.json').exists():
                    if (Path(job['output'])/'RESULT.json').exists():break
                    if Path(current['shared_latch']).exists():raise RuntimeError('Observer failure before handoff.')
                    time.sleep(.2)
                continue
        time.sleep(1)
    save(scheduler/'RESULT.json',{'schema':'entry-chain.result.v1','success':all(x.get('success') for x in completed),
        'required_block_count':len(config['jobs'])-1,'blocks':completed,'CPU_policy':'unlimited',
        'proof_acceptance':'Per-block evidence. Root review remains separate.','public_contracts_changed':False})
    public={'schema':'entry-chain.public-result.v1','success':all(x.get('success') for x in completed),
        'finished_all_blocks':len(completed)==len(config['jobs'])-1,
        'blocks':[{'pc':row['block'],'status':row['status'],'phase':row['last_phase'],
                   'groups':row['group_counts']} for row in completed],
        'private_result':binding(scheduler/'RESULT.json')}
    import json
    if len(json.dumps(public,ensure_ascii=False).encode())>6144:
        raise ValueError('The public chain result exceeds its feedback limit.')
    save(scheduler/'PUBLIC-RESULT.json',public)
    return 0 if all(x.get('success') for x in completed) else 1


if __name__=='__main__':
    try:raise SystemExit(main())
    except Exception:
        import traceback
        # A failure never cancels another healthy controller or proof process.
        path=Path(sys.argv[1]);config=strict_loads(path.read_text());out=Path(config['scheduler_output'])
        out.mkdir(parents=True,exist_ok=True);save(out/'FAILURE.json',{'error':traceback.format_exc(),
            'healthy_jobs_not_cancelled':True});raise
