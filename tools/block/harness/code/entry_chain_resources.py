from proof_bindings import check_proof_bindings
"""Use reviewed process checks and account each owned aggregate once."""
import os,resource,time
from pathlib import Path
from entry_chain import save as atomic_json,digest,strict_loads
from check_entry_outside import ticks
from entry_chain_process import identity,sample,ProcessGone,MetadataFailure,confirmed_gone
from entry_admission.io_helpers import memory_available
P=Path(__file__).resolve().parent
MEMORY=64*1024**3


def publish_latch(path,reason,detail):
    # Exclusive creation makes the first failure immutable across workers.
    import json
    try:
        fd=os.open(path,os.O_WRONLY|os.O_CREAT|os.O_EXCL,0o600)
    except FileExistsError:return
    with os.fdopen(fd,'w') as stream:
        json.dump({'reason':reason,'detail':detail,'time_ns':time.time_ns(),
                   'healthy_current_calls_preserved':True},stream)
        stream.flush();os.fsync(stream.fileno())


def proof_actor(row):
    name=Path(row['exe']).name
    args=row['argv']
    if args[1:2]==['-B']:args=[args[0],*args[2:]]
    python_script = args[1] if name.startswith('python') and len(args)>1 else None
    return (name in ('pet','coqc','coqc.opt','rocq') or
        python_script is not None and (python_script.endswith('/complete_goals_mcp.py') or python_script.endswith('/entry_chain_provider.py') or
            python_script==str(P/'entry_chain_run.py') and args[2:3]==['--inside']))

def validate_limits(row,memory_fence_bytes=MEMORY,*,memory_job=None):
    from memory_policy import validate_job,job_fence
    if memory_job is not None:
        validate_job(memory_job)
        if memory_fence_bytes!=job_fence(memory_job):raise MetadataFailure('The actor fence differs from its bound job.')
    elif memory_fence_bytes!=MEMORY:raise MetadataFailure('A measured actor requires its bound memory job.')
    cpu=next(x.split()[3:5] for x in row['limits'].splitlines() if x.startswith('Max cpu time'))
    if cpu!=['unlimited','unlimited']:raise MetadataFailure('Finite CPU cap on owned actor.')
    if proof_actor(row) and row['effective_limits']!={'memory.max':memory_fence_bytes,'memory.swap.max':0}:
        raise MetadataFailure('Physical proof fence differs.')
    if row['effective_limits']['memory.swap.max']!=0:raise MetadataFailure('Swap fence differs.')

def normalize_cpu():
    before=resource.getrlimit(resource.RLIMIT_CPU)
    if before[1]!=resource.RLIM_INFINITY:raise ValueError('Finite inherited hard CPU limit. Launch from an unlimited parent.')
    resource.setrlimit(resource.RLIMIT_CPU,(-1,-1))
    return {'before':before,'after':resource.getrlimit(resource.RLIMIT_CPU)}

def effective(group):
    root=Path('/sys/fs/cgroup');cur=root/group.lstrip('/');values={'memory.max':[],'memory.swap.max':[]}
    while True:
        for name in values:
            f=cur/name
            if f.exists():
                text=f.read_text().strip()
                if text!='max':values[name].append(int(text))
        if cur==root:break
        cur=cur.parent
    return {k:min(v) if v else None for k,v in values.items()}

def check_operation(runtime, wait=True, *, force_full=False):
    # Scratch policy: retain exact input checks without telemetry or observers.
    from entry_chain import check_bindings
    started=time.monotonic()
    if runtime.get('harness') is not None:
        from harness_commit import check
        check(runtime['harness'])
    work=check_proof_bindings(runtime,force_full=force_full)
    report={'source_bindings_checked':True,'custom_observer':False,**work,'elapsed_seconds':time.monotonic()-started}
    if runtime.get('seed_binding_reference') and runtime.get('job_output'):
        import json
        with (Path(runtime['job_output'])/'VALIDATION-WORK.jsonl').open('a') as stream:stream.write(json.dumps(report,sort_keys=True)+'\n')
    return report
