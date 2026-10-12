"""Print read-only liveness from child records and ai-coord job logs."""

import argparse
from datetime import datetime, timezone
import json
import os
from pathlib import Path


RECORD_NAMES = frozenset({
    'CURRENT-CALL.json', 'raw-calls.json', 'RAW-CALLS.json', 'calls.json',
    'session-start-identities.json', 'session-before-closure.json', 'OWNER.json',
    'PROOF-START.json', 'FIRST-PROOF-REQUEST.json', 'CONTROLLER-START.json',
})
RECORD_SUFFIXES = ('-SERVER-OWNER.json', '-LIVE-PET.json')
PROOF_TOOLS = frozenset({'rocq_check', 'rocq_step_multi', 'rocq_compile_file', 'rocq_verify'})
MAX_RECORD_BYTES = 16 * 1024 * 1024


def read_record(path):
    if path.stat().st_size > MAX_RECORD_BYTES:
        raise ValueError('The record exceeds the read limit.')
    return json.loads(path.read_text())


def utc_time(stamp):
    if not isinstance(stamp, str):
        raise ValueError('The request time is not a string.')
    value = datetime.fromisoformat(stamp.replace('Z', '+00:00'))
    if value.tzinfo is None:
        raise ValueError('The request time has no timezone.')
    return value


def process_identity(proc, pid):
    try:
        fields = (proc / str(pid) / 'stat').read_text().rsplit(')', 1)[1].split()
        if fields[0] in ('Z', 'X'):
            return None
        return {'pid': int(pid), 'start_ticks': int(fields[19])}
    except (OSError, ValueError, IndexError):
        return None


def recorded_owners(value):
    if isinstance(value, dict):
        if isinstance(value.get('pid'), int) and isinstance(value.get('start_ticks'), int):
            yield {'pid': value['pid'], 'start_ticks': value['start_ticks']}
        for key in ('server', 'pet', 'owner', 'owned', 'owned_start_identities'):
            yield from recorded_owners(value.get(key))


def proof_requests(value):
    if isinstance(value, list):
        for row in value:
            yield from proof_requests(row)
    elif isinstance(value, dict) and value.get('tool') in PROOF_TOOLS:
        stamp = value.get('started_utc') or value.get('request_utc') or value.get('request_UTC')
        if stamp:
            arguments = value.get('arguments', {})
            if not isinstance(arguments, dict):
                raise ValueError('The request arguments are not an object.')
            command = arguments.get('body') or arguments.get('tactics') or arguments.get('file') or value['tool']
            yield {'utc': stamp, 'tool': value['tool'], 'command': command}


def record_paths(worktree):
    for root in (worktree / '_build', worktree / 'build/stock-zisk'):
        if not root.is_dir():
            continue
        for directory, children, files in os.walk(root, followlinks=False):
            relative = Path(directory).relative_to(root)
            children[:] = [name for name in children
                           if name not in ('agents', 'default', 'install', 'sources', 'archive')
                           and not (Path(directory) / name).is_symlink()]
            if len(relative.parts) >= 7:
                children.clear()
            for name in files:
                if name in RECORD_NAMES or name.endswith(RECORD_SUFFIXES):
                    yield Path(directory) / name


def belongs(path, worktree):
    try:
        Path(path).relative_to(worktree)
        return True
    except ValueError:
        return False


def running_jobs(worktree, proc):
    """Read only watch-run arguments. Never emit the complete command line."""
    rows = []
    for entry in proc.iterdir():
        if not entry.name.isdecimal():
            continue
        owner = process_identity(proc, entry.name)
        if owner is None:
            continue
        try:
            args = (entry / 'cmdline').read_bytes().decode(errors='replace').split('\0')
            if 'watch-run' not in args or '--log' not in args or '--label' not in args:
                continue
            separator = args.index('--')
            command = args[separator + 1:]
            cwd_matches = belongs((entry / 'cwd').resolve(), worktree)
            if not cwd_matches and not any(belongs(arg, worktree) for arg in command if arg.startswith('/')):
                continue
            log = Path(args[args.index('--log') + 1])
            rows.append({**owner, 'label': args[args.index('--label') + 1], 'log': str(log),
                         'log_bytes': log.stat().st_size if log.exists() else None,
                         'log_modified_utc': datetime.fromtimestamp(log.stat().st_mtime, timezone.utc).isoformat()
                         if log.exists() else None})
        except (OSError, ValueError, IndexError):
            continue
    return sorted(rows, key=lambda row: row['pid'])


def process_start_utc(proc, ticks):
    try:
        boot = next(int(line.split()[1]) for line in (proc / 'stat').read_text().splitlines()
                    if line.startswith('btime '))
        return datetime.fromtimestamp(boot + ticks / os.sysconf('SC_CLK_TCK'), timezone.utc).isoformat()
    except (OSError, ValueError, StopIteration):
        return None


def inspect(worktree, *, proc=Path('/proc'), paths=None):
    worktree = Path(worktree).resolve()
    jobs = running_jobs(worktree, proc)
    sessions, requests, unavailable = [], [], []
    for path in paths if paths is not None else record_paths(worktree):
        try:
            value = read_record(path)
            for owner in recorded_owners(value):
                if process_identity(proc, owner['pid']) == owner:
                    if path.name == 'OWNER.json':
                        jobs.append({**owner, 'label': path.parent.name, 'record': str(path)})
                    else:
                        sessions.append({**owner, 'record': str(path)})
            for request in proof_requests(value):
                utc_time(request['utc'])
                requests.append({**request, 'record': str(path)})
        except (OSError, ValueError, TypeError):
            unavailable.append(str(path))
    unique = {(row['pid'], row['start_ticks']): row for row in sessions}
    sessions = sorted(unique.values(), key=lambda row: row['pid'])
    active = jobs + sessions
    last = max(requests, key=lambda row: utc_time(row['utc']),
               default=None)
    return {'child': worktree.name, 'worktree': str(worktree), 'running_jobs': jobs,
            'running_sessions': sessions,
            'start_utc': min((process_start_utc(proc, row['start_ticks']) for row in active),
                             key=lambda value: value or 'z', default=None),
            'last_proof_request': last, 'unavailable_records': unavailable,
            'scope': 'Known records within seven directories. Live PID/start identities only. '
                     'A request time does not establish proof completion.'}


def line(row):
    jobs = ','.join(job['label'] for job in row['running_jobs']) or 'none'
    sessions = ','.join(str(session['pid']) for session in row['running_sessions']) or 'none'
    last = row['last_proof_request']
    command = json.dumps(last['command'], ensure_ascii=False) if last else 'unavailable'
    if len(command) > 160:
        command = command[:157] + '...'
    return (f"{row['child']} | jobs={jobs} | sessions={sessions} | "
            f"start={row['start_utc'] or 'unavailable'} | "
            f"last_proof={last['utc'] if last else 'unavailable'} | "
            f"command={command} | "
            f"unavailable_records={len(row['unavailable_records'])}")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('worktrees', nargs='+', type=Path)
    parser.add_argument('--json', action='store_true', help='Emit records with source locators.')
    args = parser.parse_args()
    for worktree in args.worktrees:
        if not worktree.is_dir():
            parser.error(f'The worktree directory does not exist: {worktree}')
        row = inspect(worktree)
        print(json.dumps(row, ensure_ascii=False) if args.json else line(row))


if __name__ == '__main__':
    main()
