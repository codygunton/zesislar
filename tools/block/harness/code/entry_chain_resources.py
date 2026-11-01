from proof_bindings import check_proof_bindings
"""Use reviewed process checks and account each owned aggregate once."""
import os,resource,time
from contextlib import contextmanager
from contextvars import ContextVar
from threading import RLock
from pathlib import Path
from entry_chain import save as atomic_json,digest,strict_loads
from check_entry_outside import ticks
from entry_chain_process import identity,sample,ProcessGone,MetadataFailure,confirmed_gone
from entry_admission.io_helpers import memory_available
P=Path(__file__).resolve().parent
MEMORY=64*1024**3
_SESSION_VALIDATION=ContextVar('provider_session_validation',default=None)


class SessionValidation:
    """Reuse full validation only within one unchanged runtime-file context."""
    def __init__(self,path,expected):
        self.path=Path(path).absolute();self.expected=expected;self.pid=os.getpid()
        self.lock=RLock();self.validator=None;self.previous_identity=None;self.work=None
        self.full_attempts=0;self.full_completed=0;self.reused=0;self.final=None

    def identity(self):
        from binding_cache import identity
        return str(self.path.resolve(strict=True)),identity(self.path)

    def check(self,path,expected,validate,force=False):
        from binding_cache import digest as checked_digest,force_hashing
        with self.lock:
            if os.getpid()!=self.pid:
                raise ValueError('The validation session belongs to another process.')
            if Path(path).absolute()!=self.path or expected!=self.expected:
                raise ValueError('The session names another runtime envelope.')
            self.validator=validate
            before=self.identity()
            if not force and self.work is not None and before==self.previous_identity:
                if self.identity()!=before:
                    self.work=None;self.previous_identity=None
                    raise ValueError('The session runtime changed during its identity check.')
                self.reused+=1
                return self.work,True
            self.full_attempts+=1
            self.work=None;self.previous_identity=None
            with force_hashing(True):
                if checked_digest(self.path)!=self.expected:
                    raise ValueError('The bound session runtime bytes changed.')
                work=validate()
            if self.identity()!=before:
                raise ValueError('The session runtime changed during full validation.')
            self.previous_identity=before;self.work=work;self.full_completed+=1
            return work,False

    def finish(self):
        started=time.monotonic()
        if self.validator is None:
            self.final={'success':False,'available':False,
                        'reason':'Execution refused before runtime validation reached a loaded envelope.'}
            return
        try:
            work,_=self.check(self.path,self.expected,self.validator,force=True)
            self.final={'success':True,'available':True,'source_bindings_checked':True,
                        **work,'elapsed_seconds':time.monotonic()-started}
        except BaseException as error:
            self.final={'success':False,'available':True,'error':repr(error),
                        'elapsed_seconds':time.monotonic()-started}
            raise

    def report(self):
        return {'runtime_path':str(self.path),'runtime_sha256':self.expected,'pid':self.pid,
                'full_validation_attempts':self.full_attempts,
                'full_validations_completed':self.full_completed,
                'reused_operation_checks':self.reused,'final_validation':self.final}


@contextmanager
def session_validation(path,expected):
    state=SessionValidation(path,expected);token=_SESSION_VALIDATION.set(state)
    try:
        yield state
    finally:
        try:
            state.finish()
        finally:
            _SESSION_VALIDATION.reset(token)


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
    session=_SESSION_VALIDATION.get()
    def validate():
        if runtime.get('harness') is not None:
            from harness_commit import check
            check(runtime['harness'])
        return check_proof_bindings(runtime,force_full=force_full or session is not None)
    if session is None:
        work=validate();reused=False
    else:
        work,reused=session.check(runtime['runtime_path'],runtime['runtime_sha256'],validate,force_full)
    if reused:
        work=dict(work,cached_proof_bindings=work.get('proof_bindings_checked',0),proof_bindings_checked=0)
        for name in ['shared_seed_files_checked','cell_delta_files_checked']:
            if name in work:
                work['cached_'+name]=work[name];work[name]=0
    report={'source_bindings_checked':not reused,'validation_reused':reused,
            'custom_observer':False,**work,'elapsed_seconds':time.monotonic()-started}
    if runtime.get('seed_binding_reference') and runtime.get('job_output'):
        import json
        with (Path(runtime['job_output'])/'VALIDATION-WORK.jsonl').open('a') as stream:stream.write(json.dumps(report,sort_keys=True)+'\n')
    return report
