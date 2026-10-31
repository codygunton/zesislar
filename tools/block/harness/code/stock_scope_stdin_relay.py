#!/usr/bin/env python3
"""Keep a stdio input pipe open across the stock guard's background scope."""
import argparse
import json
import os
from pathlib import Path
import signal
import stat
import subprocess
import sys


def startticks(pid):
    text=Path(f'/proc/{pid}/stat').read_text()
    return int(text[text.rfind(')')+2:].split()[19])


def enter(owner, ticks, fd, device, inode, command):
    if startticks(owner)!=ticks:
        raise ValueError('The input-pipe owner identity changed.')
    opened=os.open(f'/proc/{owner}/fd/{fd}',os.O_RDONLY)
    try:
        info=os.fstat(opened)
        if (info.st_dev,info.st_ino)!=(device,inode) or not stat.S_ISFIFO(info.st_mode):
            raise ValueError('The retained input pipe identity changed.')
        if startticks(owner)!=ticks:
            raise ValueError('The input-pipe owner identity changed during open.')
        os.dup2(opened,0)
    finally:os.close(opened)
    environment = dict(os.environ)
    environment.pop('ZESU_COQC_RESERVATION', None)
    environment.pop('ZESU_COQC_SCOPE', None)
    os.execve(command[0], command, environment)


def scope(guard, command, receipt):
    original=os.dup(0)
    info=os.fstat(original)
    if not stat.S_ISFIFO(info.st_mode):
        os.close(original)
        raise ValueError('The MCP input must be a pipe.')
    owner=os.getpid();ticks=startticks(owner)
    argv=[guard,'scope','entry-pilot-mcp','--',sys.executable,str(Path(__file__).resolve()),'enter',
          str(owner),str(ticks),str(original),str(info.st_dev),str(info.st_ino),'--',*command]
    record={'owner_pid':owner,'owner_startticks':ticks,'source_fd':original,
            'source_device':info.st_dev,'source_inode':info.st_ino,'guard_argv':argv,
            'guard_unchanged':True,'stdin_only':True}
    Path(receipt).write_text(json.dumps(record,indent=2)+'\n')
    child=None
    def forward(number,_frame):
        if child is not None and child.poll() is None:
            try:os.killpg(child.pid,number)
            except ProcessLookupError:pass
    old={number:signal.signal(number,forward) for number in (signal.SIGTERM,signal.SIGINT,signal.SIGHUP)}
    try:
        child=subprocess.Popen(argv,stdin=subprocess.DEVNULL,start_new_session=True)
        code=child.wait()
        record['guard_exit']=code
        Path(receipt).write_text(json.dumps(record,indent=2)+'\n')
        return code
    finally:
        os.close(original)
        for number,handler in old.items():signal.signal(number,handler)


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('mode',choices=['scope','enter'])
    parser.add_argument('arguments',nargs=argparse.REMAINDER)
    args=parser.parse_args()
    if args.mode=='enter':
        values=args.arguments
        if len(values)<7 or values[5]!='--':parser.error('The enter command is incomplete.')
        enter(*(int(x) for x in values[:5]),values[6:])
    else:
        values=args.arguments
        if len(values)<6 or values[0]!='--guard' or values[2]!='--receipt' or values[4]!='--':
            parser.error('The scope command needs its guard, receipt, and pinned command.')
        raise SystemExit(scope(values[1],values[5:],values[3]))


if __name__=='__main__':main()
