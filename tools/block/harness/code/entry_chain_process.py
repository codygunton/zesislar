"""Treat a stable live identity with unreadable metadata as an observer failure."""
from pathlib import Path
import os
import re

class ProcessGone(Exception):
    def __init__(self,pid,start,reason,evidence=None):
        self.pid,self.start,self.reason,self.evidence=pid,start,reason,evidence
        super().__init__(f"{pid}:{start}: {reason}")

class MetadataFailure(RuntimeError):
    pass

def identity(proc):
    fields=(proc/"stat").read_text().rsplit(")",1)[1].split()
    if len(fields)<20 or not fields[19].isdigit():
        raise MetadataFailure("Malformed process stat: "+str(proc))
    return fields

PF_EXITING = 0x00000004

def exit_evidence(fields):
    if not fields[6].isdigit():raise MetadataFailure('Malformed process flags')
    return {'state':fields[0],'start_ticks':fields[19],'flags_decimal':int(fields[6]),
            'PF_EXITING':PF_EXITING,'kernel_exit_started':bool(int(fields[6]) & PF_EXITING),
            'stat_fields_after_comm':list(fields),'closure_established':False}

def confirmed_gone(proc,start,evidence=None):
    try:current=identity(proc)
    except (FileNotFoundError,ProcessLookupError):return "identity_absent"
    if current[19]!=start:return "pid_reused"
    if current[0] in {"Z","X"}:return "nonrunning_identity_"+current[0]
    found=exit_evidence(current)
    if evidence is not None:evidence.update(found)
    if found['kernel_exit_started']:return 'kernel_exit_started_PF_EXITING'
    return None

def sample(proc,expected_start=None,*,cgroup_root=Path("/sys/fs/cgroup")):
    proc=Path(proc)
    try:fields=identity(proc)
    except (FileNotFoundError,ProcessLookupError):raise ProcessGone(int(proc.name),expected_start,"identity_absent")
    start=fields[19]
    if expected_start is not None and start!=expected_start:
        raise ProcessGone(int(proc.name),expected_start,"pid_reused")
    if fields[0] in {"Z","X"}:raise ProcessGone(int(proc.name),start,"nonrunning_identity_"+fields[0])
    before=exit_evidence(fields)
    if before['kernel_exit_started']:raise ProcessGone(int(proc.name),start,'kernel_exit_started_PF_EXITING',before)
    try:
        status=(proc/"status").read_text()
        matches=re.findall(r"^VmHWM:\s*(\d+)\s+kB\s*$",status,re.M)
        if len(matches)!=1:raise MetadataFailure("Missing or repeated live VmHWM: "+str(proc))
        argv=[x.decode() for x in (proc/"cmdline").read_bytes().split(b"\0") if x]
        if not argv:raise MetadataFailure("Empty live command line: "+str(proc))
        exe=os.readlink(proc/"exe")
        cwd=os.readlink(proc/"cwd")
        groups=(proc/"cgroup").read_text()
        unified=[x.split(":",2)[2] for x in groups.splitlines() if x.startswith("0::")]
        if len(unified)!=1:raise MetadataFailure("Missing or repeated unified cgroup: "+str(proc))
        cg=cgroup_root/unified[0].lstrip("/")
        memory=(cg/"memory.max").read_text().strip()
        swap=(cg/"memory.swap.max").read_text().strip()
        limits=(proc/"limits").read_text()
        after=identity(proc)
        if after[19]!=start:raise ProcessGone(int(proc.name),start,"pid_reused")
        if after[0] in {"Z","X"}:raise ProcessGone(int(proc.name),start,"nonrunning_identity_"+after[0])
        after_evidence=exit_evidence(after)
        if after_evidence['kernel_exit_started']:raise ProcessGone(int(proc.name),start,'kernel_exit_started_PF_EXITING',after_evidence)
        if argv[0]=="/home/cody/islaris/_opam/bin/coqc" and exe!=argv[0]:
            raise MetadataFailure("Stable live compiler executable differs: "+str(proc))
        return {"pid":int(proc.name),"startticks":start,"state":after[0],"argv":argv,
            "exe":exe,"cwd":cwd,"lifecycle_evidence":after_evidence,"VmHWM_KiB":int(matches[0]),"cgroup":unified[0],
            "memory_max":memory,"memory_swap_max":swap,"limits":limits,
            "kind":"physical_coqc" if argv[0]=="/home/cody/islaris/_opam/bin/coqc" else "other_owned_process"}
    except ProcessGone:raise
    except (OSError,ValueError,IndexError,UnicodeError,MetadataFailure) as error:
        evidence={}
        reason=confirmed_gone(proc,start,evidence)
        if reason:raise ProcessGone(int(proc.name),start,reason,evidence) from error
        raise MetadataFailure(f"Live identity {proc.name}:{start} metadata failed: {error}") from error
