#!/usr/bin/env python3
"""Run one compiler command and record its own exit status, CPU, peak memory and output.

usage: measure.py OUT [--] CMD...

Writes OUT (JSON) when CMD starts ({"started_utc", "command", ...}, no "returncode"), and again
when it ends. The final record holds CMD's exit status as `returncode` (negative: killed by that
signal), CPU seconds, peak RSS, wall time, the command, its working directory, the load-path
environment, the SHA-256 of every `.v` argument at launch, and the path and SHA-256 of CMD's
combined output, which is also streamed to this process's stdout. OUT.log beside OUT holds that
output.

The exit status of a guard, perf or shell wrapper around this script is not CMD's status: the
resource guard's batch and scope return 0 for a failed compile. Read `returncode` from OUT.
This script exits with CMD's status (128 + signal for a signal death).
"""
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import time

ENVIRONMENT = ('OCAMLPATH', 'COQPATH', 'ROCQPATH', 'COQLIB', 'ROCQLIB', 'COQCORELIB', 'COQ_COLOR')


def sha256(path):
    digest = hashlib.sha256()
    with open(path, 'rb') as handle:
        for block in iter(lambda: handle.read(1 << 20), b''):
            digest.update(block)
    return digest.hexdigest()


def now():
    return datetime.now(timezone.utc).isoformat()


def write(path, record):
    pending = path.with_name(path.name + '.pending')
    pending.write_text(json.dumps(record, indent=1) + '\n')
    pending.replace(path)


def main(argv):
    if len(argv) < 2:
        print(__doc__, file=sys.stderr)
        return 2
    out, command = Path(argv[0]), argv[1:]
    if command[:1] == ['--']:
        command = command[1:]
    if not command:
        print(__doc__, file=sys.stderr)
        return 2
    log = out.with_name(out.name + '.log')
    record = {'schema': 'measure/1', 'command': command, 'cwd': os.getcwd(),
              'executable': os.path.realpath(shutil.which(command[0]) or command[0]),
              'environment': {name: os.environ[name] for name in ENVIRONMENT if name in os.environ},
              'inputs': {arg: sha256(arg) for arg in command[1:] if arg.endswith('.v') and Path(arg).is_file()},
              'started_utc': now(), 'log': str(log.resolve())}
    write(out, record)
    start = time.monotonic()
    output = hashlib.sha256()
    with log.open('wb') as saved:
        process = subprocess.Popen(command, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        for chunk in iter(lambda: process.stdout.read1(1 << 16), b''):
            saved.write(chunk)
            saved.flush()
            output.update(chunk)
            sys.stdout.buffer.write(chunk)
            sys.stdout.buffer.flush()
        _, status, usage = os.wait4(process.pid, 0)
    code = os.waitstatus_to_exitcode(status)
    record.update(returncode=code, cpu_user=usage.ru_utime, cpu_sys=usage.ru_stime,
                  max_rss_kib=usage.ru_maxrss, wall=time.monotonic() - start, ended_utc=now(),
                  log_sha256=output.hexdigest())
    write(out, record)
    return code if code >= 0 else 128 - code


if __name__ == '__main__':
    sys.exit(main(sys.argv[1:]))
