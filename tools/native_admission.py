"""Shared admission checks for future native and MCP controllers.

Controllers supply their existing verified server-owner records. This helper
does not register jobs or reserve slots. Controllers must call the normal
guard wait, then take a fresh snapshot before launch. The standing policy
permits eight native slots and one owned MCP session per child.
"""

import os
import re
from pathlib import Path
import subprocess


NAMES = frozenset({'coqc', 'coqc.byte', 'coqc.opt', 'rocq', 'rocqtop', 'coqtop', 'pet'})
GIB = 1024 ** 3
COMPILER_LIMIT = 48
DEFAULT_MEMORY_LIMIT = 6 * GIB
PROBE_MEMORY_LIMIT = 64 * GIB


def status(entry):
    fields = dict(line.split(':', 1) for line in (entry / 'status').read_text().splitlines()
                  if ':' in line)
    return int(fields['Pid']), fields['State'].split()[0]


def unique_processes(records):
    found = {}
    for record in records:
        pid = record['pid']
        if type(pid) is not int or pid <= 0:
            raise ValueError('The process PID must be a positive integer.')
        if record['comm'] not in NAMES or record['state'] in ('Z', 'X'):
            continue
        previous = found.get(pid)
        if previous is not None and previous != record:
            raise ValueError('The duplicate process records differ.')
        found[pid] = record
    return [found[pid] for pid in sorted(found)]


def inventory(proc=Path('/proc')):
    records = []
    for entry in proc.iterdir():
        if not entry.name.isdecimal():
            continue
        try:
            name = (entry / 'comm').read_text().strip()
            if name not in NAMES:
                continue
            pid, state = status(entry)
        except (FileNotFoundError, ProcessLookupError):
            continue
        if pid != int(entry.name):
            raise ValueError('The process status PID differs from its path.')
        records.append({'pid': pid, 'comm': name, 'state': state})
    return unique_processes(records)


def owned_session_live(owner, proc=Path('/proc')):
    """Check one previously verified owner by PID and retained start ticks."""
    entry = proc / str(owner['server_pid'])
    try:
        pid, state = status(entry)
        fields = (entry / 'stat').read_text().rsplit(')', 1)[1].split()
    except (FileNotFoundError, ProcessLookupError):
        return False
    if pid != owner['server_pid']:
        raise ValueError('The owner status PID differs from its retained identity.')
    return state not in ('Z', 'X') and int(fields[19]) == owner['server_start_ticks']


def clean_environment(environment):
    return {key: value for key, value in environment.items()
            if not key.startswith(('ZESU_', 'ROCQ_', 'COQC_'))
            and key not in ('COQPATH', 'COQBIN', 'COQC')}


def snapshot(guard, child, owned_sessions, *, proc=Path('/proc'), environment=None):
    if not child:
        raise ValueError('The controller must supply its child identity.')
    original_env = os.environ if environment is None else environment
    env = clean_environment(original_env)
    writer = original_env.get('ZESU_WRITER_ID', '')
    if writer:
        if not re.fullmatch(r'[a-zA-Z0-9._-]+', writer):
            raise ValueError('The writer identity is invalid.')
        env['ZESU_WRITER_ID'] = writer

    def query(command):
        return subprocess.check_output([str(guard), command], env=env, text=True).strip()

    limit = int(query('native-limit'))
    if limit != 8:
        raise ValueError('The native admission policy differs from eight arms.')
    processes = inventory(proc)
    # The caller obtains these records through the certificate owner RPC. Do
    # not infer a child identity from process arguments or environment values.
    sessions = [owner for owner in owned_sessions if owner['child'] == child
                and owned_session_live(owner, proc)]
    return {'child': child, 'writer_identity': writer, 'native_limit': limit, 'live_interpreters': processes,
            'owned_sessions_for_child': sessions, 'compiler_count': int(query('coqc-count')),
            'normal_guard_hold': query('hold'), 'gate_status': query('lock-status')}


def memory_reason(requested_memory_bytes, budget_policy):
    if type(requested_memory_bytes) is not int or requested_memory_bytes <= 0:
        return 'The arm memory request must be a positive integer.'
    if budget_policy is None:
        if requested_memory_bytes > DEFAULT_MEMORY_LIMIT:
            return 'The default arm memory request must not exceed six GiB.'
        return None
    # Use the existing coqc_primary probe policy. Controllers record the
    # issue10 probe before launch and validate the actual child limits.
    if (not isinstance(budget_policy, dict) or budget_policy.get('kind') != 'probe'
            or 'cpu_seconds' not in budget_policy or budget_policy['cpu_seconds'] is not None
            or 'wall_seconds' not in budget_policy or budget_policy['wall_seconds'] is not None
            or budget_policy.get('memory_kib') != PROBE_MEMORY_LIMIT // 1024
            or budget_policy.get('optimization_debt') != 'issue#10'
            or requested_memory_bytes != PROBE_MEMORY_LIMIT):
        return 'The probe requires issue10, 64 GiB, unlimited CPU, and no wall cutoff.'
    return None


def reason(observed, *, kind, requested_memory_bytes=DEFAULT_MEMORY_LIMIT, budget_policy=None):
    """Check admission, with an explicit policy for issue10 unlimited probes.

    This check does not set child limits or record a probe on issue10.
    Controllers must perform both operations and use a fresh snapshot.
    """
    if kind not in ('native', 'mcp'):
        raise ValueError('The admission kind must be native or mcp.')
    policy_reason = memory_reason(requested_memory_bytes, budget_policy)
    if policy_reason is not None:
        return policy_reason
    if observed['normal_guard_hold'] != 'none':
        return observed['normal_guard_hold']
    if observed['gate_status'] != 'no gate lock' and not observed.get('writer_identity'):
        return 'The gate holds admission.'
    if observed['compiler_count'] < 0 or observed['compiler_count'] >= COMPILER_LIMIT:
        return 'The forty-eight compiler limit holds admission.'
    if observed['native_limit'] != 8:
        raise ValueError('The native admission policy differs from eight arms.')
    if len(unique_processes(observed['live_interpreters'])) >= observed['native_limit']:
        return 'The eight native slots are occupied.'
    if kind == 'mcp' and observed['owned_sessions_for_child']:
        return 'The child already owns an MCP session.'
    return None
