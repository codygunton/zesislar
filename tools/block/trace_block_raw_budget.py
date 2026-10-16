"""Account raw writes across processes. The locked ledger has a fixed size."""
import argparse,contextlib,fcntl,json,os,stat,sys,threading
from pathlib import Path
LEDGER_BYTES=8192
LIMIT_BYTES=2_000_000_000
CONTROL_RESERVE=1_048_576
class BudgetExceeded(OSError):pass
_LOCKS={}
_LOCKS_GUARD=threading.Lock()
def _thread_lock(path):
    with _LOCKS_GUARD:return _LOCKS.setdefault(str(Path(path).resolve()),threading.RLock())

def _encode(value):
    data=json.dumps(value,sort_keys=True,separators=(',',':')).encode()
    if len(data)>=LEDGER_BYTES:raise ValueError('The raw ledger exceeds its fixed size')
    return data+b' '*(LEDGER_BYTES-len(data)-1)+b'\n'

class RawBudget:
    def __init__(self,ledger):self.ledger=Path(ledger)
    @classmethod
    def create(cls,root,*,limit=LIMIT_BYTES,control_reserve=CONTROL_RESERVE):
        if type(limit)is not int or not LEDGER_BYTES<limit<=LIMIT_BYTES:
            raise ValueError('The raw limit must not exceed 2000000000 bytes')
        if type(control_reserve)is not int or not 0<=control_reserve<limit-LEDGER_BYTES:
            raise ValueError('The control reserve must stay inside the raw limit')
        root=Path(root).resolve();root.mkdir(parents=True,exist_ok=True)
        ledger=root/'evidence/RAW-BUDGET.json';ledger.parent.mkdir(parents=True,exist_ok=True)
        if ledger.exists():raise FileExistsError(ledger)
        used=LEDGER_BYTES
        for directory,_,names in os.walk(root,followlinks=False):
            for name in names:
                value=(Path(directory)/name).lstat()
                if stat.S_ISREG(value.st_mode)or stat.S_ISLNK(value.st_mode):used+=value.st_size
        if used+control_reserve>=limit:raise ValueError('The initial raw files exceed the writer allowance')
        value=dict(schema=1,root=str(root),limit_bytes=limit,control_reserve_bytes=control_reserve,
            used_bytes=used,complete=True,denied_writes=0,first_denial=None)
        encoded=_encode(value)
        descriptor=os.open(ledger,os.O_WRONLY|os.O_CREAT|os.O_EXCL|os.O_CLOEXEC,0o600)
        try:
            fcntl.lockf(descriptor,fcntl.LOCK_EX)
            offset=0
            while offset<len(encoded):offset+=os.write(descriptor,encoded[offset:])
            os.fsync(descriptor)
        finally:os.close(descriptor)
        return cls(ledger)
    @contextlib.contextmanager
    def locked(self):
        local=_thread_lock(self.ledger);local.acquire()
        descriptor=None
        try:
            descriptor=os.open(self.ledger,os.O_RDWR|os.O_CLOEXEC)
            fcntl.lockf(descriptor,fcntl.LOCK_EX)
            data=os.read(descriptor,LEDGER_BYTES+1)
            if len(data)!=LEDGER_BYTES:raise ValueError('The raw ledger size changed')
            value=json.loads(data)
            yield descriptor,value
        finally:
            if descriptor is not None:os.close(descriptor)
            local.release()
    def read(self):
        with self.locked()as(_,value):return value
    def reserve(self,path,count,*,control=False):
        if type(count)is not int or not 0<=count<=sys.maxsize:raise ValueError('The raw reservation size is invalid')
        path=Path(path)
        with self.locked()as(descriptor,value):
            root=Path(value['root']);resolved=path.parent.resolve()/path.name
            if resolved==self.ledger or root not in resolved.parents:raise ValueError('The raw write leaves its owned root')
            maximum=value['limit_bytes']-(0 if control else value['control_reserve_bytes'])
            denied=(not control and not value['complete'])or count>maximum-value['used_bytes']
            if denied:
                value['complete']=False;value['denied_writes']+=1
                if value['first_denial']is None:value['first_denial']=dict(path=str(resolved.relative_to(root)).encode('utf-8')[:512].decode('utf-8',errors='ignore'),requested_bytes=count,channel='control'if control else'data')
            else:value['used_bytes']+=count
            os.lseek(descriptor,0,os.SEEK_SET);encoded=_encode(value);offset=0
            while offset<len(encoded):offset+=os.write(descriptor,encoded[offset:])
        if denied:raise BudgetExceeded('The raw writer reached its byte ceiling')
    def write(self,path,blocks,*,control=False):
        path=Path(path);self.reserve(path,0,control=control);path.parent.mkdir(parents=True,exist_ok=True)
        descriptor=os.open(path,os.O_WRONLY|os.O_CREAT|os.O_EXCL|os.O_NOFOLLOW,0o600)
        try:
            for block in blocks:
                if not isinstance(block,bytes):raise TypeError('The raw writer requires bytes')
                for offset in range(0,len(block),65536):
                    piece=block[offset:offset+65536];self.reserve(path,len(piece),control=control)
                    position=0
                    while position<len(piece):position+=os.write(descriptor,piece[position:])
        finally:os.close(descriptor)

def from_environment(path):
    ledger=os.environ.get('ZESU_TRACE_RAW_BUDGET')
    if not ledger:return None
    budget=RawBudget(ledger);root=Path(budget.read()['root'])
    lexical=Path(os.path.abspath(path))
    resolved=lexical.parent.resolve()/lexical.name
    if lexical==root or root in lexical.parents:
        if resolved==root or root not in resolved.parents:
            raise ValueError('The raw write follows a directory link outside its root')
        return budget
    return budget if resolved!=root and root in resolved.parents else None

def main():
    parser=argparse.ArgumentParser();parser.add_argument('--ledger',required=True)
    parser.add_argument('--destination',required=True);parser.add_argument('--control',action='store_true');args=parser.parse_args()
    budget=RawBudget(args.ledger)
    def blocks():
        while True:
            data=sys.stdin.buffer.read(65536)
            if not data:return
            yield data
    try:budget.write(args.destination,blocks(),control=args.control)
    except BudgetExceeded:
        for _ in blocks():pass
        return 75
    except (OSError,ValueError,TypeError):
        for _ in blocks():pass
        return 74
    return 0
if __name__=='__main__':raise SystemExit(main())

def write_bytes(path,payload,*,control=False):
    budget=from_environment(path)
    if budget is None:
        Path(path).write_bytes(payload)
    else:budget.write(path,[payload],control=control)

def copy_file(source,destination):
    budget=from_environment(destination)
    if budget is None:
        import shutil
        return shutil.copy2(source,destination)
    with Path(source).open('rb')as stream:
        budget.write(destination,iter(lambda:stream.read(65536),b''))
    os.chmod(destination,Path(source).stat().st_mode & 0o777)
