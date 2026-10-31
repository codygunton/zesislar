#!/usr/bin/env python3
"""Collect cold-cache user-space instructions around an exact compiler command.

Call prepare() immediately before Popen(), then finish() after the process exits.
The caller retains its output, resource telemetry, guard, and exit-code handling.
"""

import csv
import hashlib
import math
import os
from pathlib import Path
import shutil
import stat


CACHE_NAMES = ('.lia.cache', '.nia.cache', '.csdp.cache')


def clear_caches(cwd, output):
    cwd, output = Path(cwd).resolve(), Path(output).resolve()
    if not cwd.is_dir() or cwd.stat().st_uid != os.geteuid():
        raise ValueError('The compiler directory must exist and belong to this user.')
    rows = []
    for name in CACHE_NAMES:
        path = cwd / name
        try:
            before = path.lstat()
        except FileNotFoundError:
            rows.append(dict(path=str(path), present=False))
            continue
        if not stat.S_ISREG(before.st_mode) or before.st_uid != os.geteuid():
            raise ValueError('A compiler cache must be a regular file owned by this user: ' + str(path))
        retained = output / 'cache-before' / name
        retained.parent.mkdir(parents=True, exist_ok=True)
        if retained.exists():
            raise ValueError('A retained compiler cache already exists.')
        from clone_copy import copyfile
        copyfile(path, retained)
        after = path.lstat()
        identity = lambda info: (info.st_dev, info.st_ino, info.st_size, info.st_mtime_ns, info.st_ctime_ns)
        if identity(before) != identity(after):
            raise ValueError('A compiler cache changed before removal: ' + str(path))
        path.unlink()
        rows.append(dict(path=str(path), present=True, retained=str(retained),
                         sha256=hashlib.sha256(retained.read_bytes()).hexdigest(),
                         size=before.st_size, removed=True))
    return rows


def parse_stat(text):
    records = []
    for fields in csv.reader(text.splitlines()):
        if not fields or not fields[0].strip() or fields[0].lstrip().startswith('#'):
            continue
        if len(fields) < 5 or fields[2].strip() != 'instructions:u':
            raise ValueError('The perf output contains an unexpected event or row.')
        count, runtime, percent = fields[0].strip(), fields[3].strip(), fields[4].strip()
        if not count.isdecimal():
            raise ValueError('The perf instruction count is unavailable or invalid.')
        try:
            runtime, percent = float(runtime), float(percent)
        except ValueError as error:
            raise ValueError('The perf running time is invalid.') from error
        if int(count) <= 0 or not math.isfinite(runtime) or runtime <= 0:
            raise ValueError('The perf instruction count or running time is not positive.')
        if not math.isfinite(percent) or percent != 100:
            raise ValueError('The perf instruction counter did not run for the complete workload.')
        records.append(dict(user_instructions=int(count), event='instructions:u',
                            event_runtime_ns=runtime, running_percent=percent))
    if len(records) != 1:
        raise ValueError('The perf output requires exactly one instruction record.')
    return records[0]


def prepare(command, output, cwd=None):
    output = Path(output).resolve()
    output.mkdir(parents=True, exist_ok=True)
    perf_stat = output / 'perf-stat.csv'
    if perf_stat.exists():
        raise ValueError('A perf result already exists.')
    cwd = Path(cwd or Path.cwd()).resolve()
    perf = shutil.which('perf')
    if perf is None:
        raise ValueError('The perf executable is unavailable.')
    caches = clear_caches(cwd, output)
    argv = [perf, 'stat', '-x,', '--no-big-num', '--no-scale', '-e', 'instructions:u',
            '--output', str(perf_stat), '--', *map(str, command)]
    return dict(command=argv, workload_command=list(map(str, command)), cwd=str(cwd),
                perf_stat=str(perf_stat), cache_removals=caches,
                decision_metric='user-space instructions',
                cpu_scope='perf driver plus compiler; retained child rusage')



def workload_pid(perf_pid, command, proc_root=Path('/proc')):
    """Find the direct perf child with the exact measured executable."""
    directory = proc_root / str(perf_pid)
    try:
        children = (directory / 'task' / str(perf_pid) / 'children').read_text().split()
    except (FileNotFoundError, ProcessLookupError):
        return None
    matches = []
    for child in children:
        try:
            argv = (proc_root / child / 'cmdline').read_bytes().split(b'\0')
        except (FileNotFoundError, ProcessLookupError):
            continue
        if argv[0].decode() == str(command[0]):
            matches.append(int(child))
    if len(matches) > 1:
        raise ValueError('The perf workload has multiple matching compiler processes.')
    return matches[0] if matches else None

def finish(measurement):
    path = Path(measurement['perf_stat'])
    text = path.read_text()
    return {**measurement, **parse_stat(text),
            'perf_stat_sha256': hashlib.sha256(path.read_bytes()).hexdigest(),
            'instruction_measurement_complete': True}
