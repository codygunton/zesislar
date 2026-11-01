"""Measure the exact physical compiler after guarded admission."""
from pathlib import Path
import hashlib,json,os,signal,subprocess,sys,time,threading
sys.path.insert(0,str(Path(__file__).resolve().parents[1]))
import run_registry

directory=Path(sys.argv[1]);path=directory/'INPUT.json';record=json.loads(path.read_text())
cwd=Path.cwd().resolve();workspace=Path(record['owned_workspace']).resolve()
if not cwd.is_relative_to(workspace):raise ValueError('The compiler cwd leaves its owned workspace.')
removed=[]
for name in ['.lia.cache','.nia.cache','.nra.cache','.csdp.cache','.bv_solve.cache']:
    cache=cwd/name
    if cache.is_symlink() or cache.is_dir():raise ValueError('The arithmetic cache is not a regular owned file.')
    existed=cache.exists()
    if existed:cache.unlink()
    removed.append({'path':str(cache),'removed':existed,'absent_after':not cache.exists()})
record.update(cwd=str(cwd),removed_cache_paths=removed)
path.write_text(json.dumps(record,indent=2)+'\n')
report=None;before=None
# Validate after guarded admission, immediately before the physical compiler.
if record.get('validation') is not None:
    from entry_chain import read_bound,save
    from compiler_snapshot import validate_compiler,sidecar_prestate,check_sidecar_prestate,compiler_outputs,_publish
    envelope=record['validation']['runtime']
    checked_runtime=read_bound(envelope)
    report=validate_compiler(checked_runtime,envelope,record['validation']['snapshot'],
        record['source'],record['physical_argv'][0],
        output_key=os.environ.get('ENTRY_CHAIN_COMPILER_SNAPSHOT_OUTPUT_KEY'))
    save(directory/'PHYSICAL-VALIDATION.json',report)
    target=(Path(record['physical_argv'][-2]) if record['physical_argv'][-3:-2]==['-o']
            else Path(record['source']['path']).with_suffix('.vo'))
    if target.suffix=='.vo':
        before=sidecar_prestate(record['source'],target,record['compiler'],checked_runtime['physical_flags'],report)
        record['sidecar_prestate']=before
        save(path,record)
# The physical compiler never receives the provider authentication key.
os.environ.pop('ENTRY_CHAIN_COMPILER_SNAPSHOT_OUTPUT_KEY',None)
if before is not None:check_sidecar_prestate(before)
started=time.monotonic();child=subprocess.Popen(record['physical_argv'],stdout=subprocess.PIPE,stderr=subprocess.PIPE)
capture_errors=[]
def retain(stream,name,descriptor):
    try:
        with (directory/name).open('xb') as saved:
            forwarding=True
            while True:
                data=stream.read(65536)
                if not data:break
                saved.write(data)
                if forwarding:
                    try:
                        view=memoryview(data)
                        while view:view=view[os.write(descriptor,view):]
                    except OSError as error:
                        capture_errors.append({'stream':name,'forward_error':repr(error)});forwarding=False
    except BaseException as error:capture_errors.append({'stream':name,'capture_error':repr(error)})
    finally:stream.close()
readers=[threading.Thread(target=retain,args=(child.stdout,'STDOUT',1)),threading.Thread(target=retain,args=(child.stderr,'STDERR',2))]
for reader in readers:reader.start()
fd=run_registry.open_pidfd(child.pid)
def forward(number,frame):
    try:run_registry.signal_pidfd(fd,number)
    except ProcessLookupError:pass
for sig in [signal.SIGTERM,signal.SIGINT,signal.SIGHUP]:signal.signal(sig,forward)
pid,status,usage=os.wait4(child.pid,0);code=os.waitstatus_to_exitcode(status);child.returncode=code;os.close(fd)
for reader in readers:reader.join()
result={'input':{'path':str(path),'sha256':hashlib.sha256(path.read_bytes()).hexdigest()},
        'physical_argv':record['physical_argv'],'returncode':code,
        'user_CPU_seconds':usage.ru_utime,'system_CPU_seconds':usage.ru_stime,
        'wall_seconds':time.monotonic()-started,'peak_rss_KiB':usage.ru_maxrss,
        'CPU_scope':'Direct physical compiler and its waited descendants.'}
result['output_capture']={'complete':not capture_errors,'errors':capture_errors,'streams':[
    {'path':str(directory/name),'sha256':hashlib.sha256((directory/name).read_bytes()).hexdigest(),'bytes':(directory/name).stat().st_size}
    for name in ['STDOUT','STDERR'] if (directory/name).is_file()]}
output_error=None
if before is not None and code==0 and not capture_errors:
    try:
        result['compiler_outputs']=compiler_outputs(target,before)
        result['output_validation']={'success':True}
    except BaseException as error:
        output_error=repr(error)
        result['output_validation']={'success':False,'error':output_error}
if report is not None:_publish(directory/'PHYSICAL-RESULT.json',result)
else:(directory/'PHYSICAL-RESULT.json').write_text(json.dumps(result,indent=2)+'\n')
if output_error:print(output_error,file=sys.stderr)
raise SystemExit(2 if capture_errors or output_error else (code if code>=0 else 128-code))
