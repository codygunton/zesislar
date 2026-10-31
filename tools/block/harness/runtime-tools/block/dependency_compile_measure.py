"""Measure the exact physical compiler after guarded admission."""
from pathlib import Path
import hashlib,json,os,signal,subprocess,sys,time
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
started=time.monotonic();child=subprocess.Popen(record['physical_argv'])
fd=run_registry.open_pidfd(child.pid)
def forward(number,frame):
    try:run_registry.signal_pidfd(fd,number)
    except ProcessLookupError:pass
for sig in [signal.SIGTERM,signal.SIGINT,signal.SIGHUP]:signal.signal(sig,forward)
pid,status,usage=os.wait4(child.pid,0);code=os.waitstatus_to_exitcode(status);child.returncode=code;os.close(fd)
result={'input':{'path':str(path),'sha256':hashlib.sha256(path.read_bytes()).hexdigest()},
        'physical_argv':record['physical_argv'],'returncode':code,
        'user_CPU_seconds':usage.ru_utime,'system_CPU_seconds':usage.ru_stime,
        'wall_seconds':time.monotonic()-started,'peak_rss_KiB':usage.ru_maxrss,
        'CPU_scope':'Direct physical compiler and its waited descendants.'}
(directory/'PHYSICAL-RESULT.json').write_text(json.dumps(result,indent=2)+'\n')
raise SystemExit(code if code>=0 else 128-code)
