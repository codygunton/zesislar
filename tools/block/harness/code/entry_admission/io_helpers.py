from pathlib import Path
from contextlib import contextmanager
import fcntl,hashlib,json,os,tempfile

def read(path):return json.loads(Path(path).read_text())

def sha(path):return hashlib.sha256(Path(path).read_bytes()).hexdigest()

def atomic_json(path,value):
 path=Path(path);fd,tmp=tempfile.mkstemp(prefix='.'+path.name+'.',suffix='.pending',dir=path.parent)
 try:
  with os.fdopen(fd,'w') as stream:json.dump(value,stream,indent=2);stream.write('\n');stream.flush();os.fsync(stream.fileno())
  os.replace(tmp,path)
 finally:
  if os.path.exists(tmp):os.unlink(tmp)

def memory_available():return int(next(x.split()[1] for x in Path('/proc/meminfo').read_text().splitlines() if x.startswith('MemAvailable:')))*1024

def validate_lock(ledger,lock):
 ledger,lock=Path(ledger),Path(lock)
 if ledger.name!='LEDGER.json' or lock!=ledger.with_name('LEDGER.lock'):raise ValueError('Use the canonical LEDGER.lock beside LEDGER.json.')

@contextmanager
def locked(ledger,lock):
 validate_lock(ledger,lock)
 with open(lock,'a+') as stream:
  fcntl.flock(stream,fcntl.LOCK_EX)
  try:yield
  finally:fcntl.flock(stream,fcntl.LOCK_UN)
