"""Close registered child controllers through their existing owned guard traps.

TERM, INT, HUP, and Python failures unwind this context. SIGKILL does not.
No process group, unregistered PID, or named foreign slice is signalled.
"""
from contextvars import ContextVar
from pathlib import Path
import os
import signal
import subprocess
import time

from entry_chain import save
from run_registry import identity, live, open_pidfd, signal_pidfd

_CURRENT=ContextVar('owned_controller_cleanup',default=None)


class ControllerExit(BaseException):
    pass


class Supervisor:
    def __init__(self, output):
        self.output=Path(output);self.owner=dict(identity(os.getpid()),uid=os.getuid())
        self.children=[];self.launching=False;self.cleaning=False;self.interrupted=None;self.closed_rows=None

    def interrupt(self, number, frame):
        self.interrupted=self.interrupted or number
        if not self.launching and not self.cleaning:raise ControllerExit(number)

    def __enter__(self):
        self.previous={number:signal.signal(number,self.interrupt)
                       for number in (signal.SIGTERM,signal.SIGINT,signal.SIGHUP)}
        self.token=_CURRENT.set(self)
        return self

    def launch(self, argv, **kwargs):
        if self.interrupted:raise ControllerExit(self.interrupted)
        self.closed_rows=None;self.launching=True
        try:
            process=subprocess.Popen(argv,**kwargs)
            record={'process':process,'actor':None,'pidfd':None,'authenticated':False}
            self.children.append(record)
            try:
                actor=identity(process.pid)
                if actor is None:
                    raise ValueError('The spawned controller identity is unavailable.')
                record['actor']=actor
                if actor['ppid']!=self.owner['pid'] or Path('/proc',str(actor['pid'])).stat().st_uid!=os.getuid():
                    raise ValueError('The launched controller has another owner.')
                record['pidfd']=open_pidfd(process.pid)
                current=identity(process.pid)
                if current is not None and (current['startticks']!=actor['startticks'] or current['ppid']!=self.owner['pid']):
                    raise ValueError('The spawned controller identity changed during registration.')
                record['authenticated']=True
            except BaseException as error:
                record['registration_error']=type(error).__name__+': '+str(error)
                raise
        finally:
            self.launching=False
        if self.interrupted:raise ControllerExit(self.interrupted)
        return process

    def cleanup(self):
        if self.closed_rows is not None:return self.closed_rows
        self.cleaning=True;rows=[]
        try:
            for record in reversed(self.children):
                process,actor,descriptor=record['process'],record['actor'],record['pidfd']
                row={'pid':process.pid,'actor':actor,'pidfd':descriptor is not None,
                     'authenticated':record['authenticated'],'signal':None}
                if not record['authenticated'] or descriptor is None:
                    row.update(closed=False,reason='Spawned child authentication is incomplete.',
                               registration_error=record.get('registration_error'))
                    rows.append(row)
                    continue
                if live(actor):
                    if identity(os.getpid())['startticks']!=self.owner['startticks']:
                        raise ValueError('The controller owner identity changed.')
                    try:signal_pidfd(descriptor,signal.SIGTERM);row['signal']='SIGTERM'
                    except ProcessLookupError:pass
                    try:signal_pidfd(descriptor,signal.SIGCONT)
                    except ProcessLookupError:pass
                if process.poll() is None:
                    try:process.wait(timeout=60)
                    except subprocess.TimeoutExpired:
                        row.update(closed=False,reason='Owned guard cleanup did not complete.')
                        rows.append(row)
                        continue
                row.update(closed=not live(actor),returncode=process.returncode)
                rows.append(row)
            if not all(row.get('closed') for row in rows):
                raise RuntimeError('Owned controller cleanup is unclosed or unknown. Claims must remain reserved.')
            self.closed_rows=rows
            return rows
        finally:
            self.cleaning=False
            self.output.mkdir(parents=True,exist_ok=True)
            save(self.output/'CONTROLLER-EXIT-CLEANUP.json',{
                'owner':self.owner,'requested_signal':self.interrupted,'children':rows,
                'all_registered_children_closed':len(rows)==len(self.children) and all(row.get('closed') for row in rows),
                'aggregate_cleanup':'Existing stock guard trap. Existing closure/release checks remain authoritative.',
                'SIGKILL_covered':False,'time_ns':time.time_ns()})

    def __exit__(self, kind, value, traceback):
        try:
            self.cleanup()
        finally:
            for record in self.children:
                if record['pidfd'] is not None:os.close(record['pidfd'])
            _CURRENT.reset(self.token)
            for number,handler in self.previous.items():signal.signal(number,handler)
        if self.interrupted:raise SystemExit(128+self.interrupted)


def launch(argv, **kwargs):
    supervisor=_CURRENT.get()
    return supervisor.launch(argv,**kwargs) if supervisor is not None else subprocess.Popen(argv,**kwargs)


def run(argv, **kwargs):
    process=launch(argv,**kwargs)
    status=process.wait()
    return subprocess.CompletedProcess(argv,status)


def cleanup():
    supervisor=_CURRENT.get()
    return supervisor.cleanup() if supervisor is not None else []


def mark():
    supervisor=_CURRENT.get()
    return len(supervisor.children) if supervisor is not None else 0


def last_child(marker=0):
    supervisor=_CURRENT.get()
    if supervisor is None or len(supervisor.children)<=marker:return None,None
    row=supervisor.children[-1]
    return row['process'],row['actor'] if row['authenticated'] else None


def children_closed(marker=0):
    supervisor=_CURRENT.get()
    if supervisor is None:return True
    return all(row['authenticated'] and row['pidfd'] is not None and
        row['process'].poll() is not None and not live(row['actor']) for row in supervisor.children[marker:])
