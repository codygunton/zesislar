"""Guard-owned controller exit peaks, separate from watchdog observations."""
from pathlib import Path
import copy
import json
import os
import signal
import stat
import subprocess
import sys
import time
import uuid

from entry_chain import binding, read_bound

SCHEMA = 'zesu.guard.controller-exit.v1'
CONTEXT_SCHEMA = 'entry-chain.controller-peak-context.v1'
ROLES = ('entry-chain-client', 'entry-pilot-mcp')
KINDS = ('declarations-dag', 'declarations-serial')


def identity(pid):
    fields = (Path('/proc') / str(pid) / 'stat').read_text().rsplit(')', 1)[1].split()
    return {'pid': pid, 'startticks': int(fields[19])}


def kind(runtime):
    from scope_bookings import controller_only
    if not controller_only(runtime):
        raise ValueError('A controller exit cannot classify a PET-capable runtime.')
    return 'declarations-dag' if runtime.get('declaration_dag') else 'declarations-serial'


def private_document(reference, reader):
    path = Path(reference['path'])
    before = reader.file_identity(path.lstat())
    if (path.resolve(strict=True) != path or before[6] != reader.uid
            or not stat.S_ISREG(before[5]) or before[5] & 0o077):
        raise ValueError('The controller peak document is not private.')
    value = read_bound(reference)
    if reader.file_identity(path.lstat()) != before:
        raise ValueError('The controller peak document changed.')
    return value, before


def runtime_context(reference, reader, *, validate_selection=True):
    value, _ = private_document(reference, reader)
    if (not isinstance(value, dict) or set(value) != {'schema','runtime','booking','role','run_kind','claim_bytes','command'}
            or value.get('schema') != CONTEXT_SCHEMA or value.get('role') not in ROLES):
        raise ValueError('The controller peak context has another role.')
    runtime = read_bound(value['runtime'])
    if value.get('run_kind') != kind(runtime):
        raise ValueError('The controller peak context has another run kind.')
    if validate_selection:
        from scope_bookings import validate_booking
        selected = validate_booking(runtime, None, value['booking'])
        field = 'client_claim_bytes' if value['role'] == ROLES[0] else 'mcp_claim_bytes'
        if value.get('claim_bytes') != selected[field]:
            raise ValueError('The controller peak context changed its booking.')
    return value, runtime


def fence(path, reader, expected):
    if (int((path/'memory.max').read_text()) != expected
            or (path/'memory.swap.max').read_text().strip() != '0'):
        raise ValueError('The controller physical fence or swap setting changed.')


def _released(reference, entry, data, reader, role, run_kind):
    import admission_memory as memory
    value, document_identity = private_document(reference, reader)
    if (not isinstance(value, dict) or list(document_identity) != entry['file_identity'] or value.get('schema') != SCHEMA
            or value.get('role') != role or value.get('run_kind') != run_kind):
        raise ValueError('The controller peak identity, role, or run kind changed.')
    amount = value.get('memory_peak_bytes')
    if (type(amount) is not int or amount <= 0 or type(value.get('returncode')) is not int
            or not 0 <= value['returncode'] <= 255
            or type(value.get('finished_ns')) is not int or value['finished_ns'] <= 0):
        raise ValueError('The controller exit lacks a normal status or positive kernel peak.')
    key = value['claim_key']
    owner = data['shell_claim_owners'][key]
    attestation = owner['guard_attestation']
    if (owner != value['owner_record'] or owner['guard_source'] != value['guard_source']
            or attestation['actor'] != value['scope_actor']
            or attestation['leaf'] != value['scope']
            or data['fixed_claims'].get(key) != 0
            or data['shell_releases'][key]['owner'] != owner['owner']
            or data['shell_releases'][key]['marker'] != owner['marker']
            or Path(owner['marker']).exists() or Path(value['scope']['scope']).exists()
            or not memory.ended_process(reader, owner['owner'])
            or not memory.ended_process(reader, value['scope_actor'])
            or not memory.ended_process(reader, value['payload_actor'])
            or value.get('payload_process_group_closed') is not True
            or data['entry_pilot_outside_owners'].get(value['root_claim_key']) != value['root_owner']):
        raise ValueError('The controller peak lacks exact closed and released ownership.')
    if reader.guard_source(value['guard_source']['path'], value['guard_source']['sha256']) != value['guard_source']:
        raise ValueError('The recorded guard identity changed.')
    context, runtime = runtime_context(value['context'], reader, validate_selection=False)
    if (context['role'] != role or kind(runtime) != run_kind
            or value.get('physical_fence_bytes') != runtime['canonical_admission']['physical_fence_bytes']):
        raise ValueError('The recorded controller context changed.')
    return value


def recorded_peak(reference, role, run_kind, *, ledger=None, reader=None):
    """Validate one pinned record. A changed selected record refuses."""
    import admission_memory as memory
    reader = memory.ScopeReader() if reader is None else reader
    ledger = Path(ledger or os.environ.get('ZESU_CANONICAL_LEDGER', memory.DEFAULT_LEDGER))
    with memory.ledger_transaction(ledger) as data:
        entries = copy.deepcopy(data.get('controller_exit_peaks', []))
        snapshot = copy.deepcopy(data)
    matches = [entry for entry in entries if isinstance(entry, dict) and entry.get('receipt') == reference]
    if len(matches) != 1:
        raise ValueError('The controller peak is not endorsed by the canonical guard.')
    return _released(reference, matches[0], snapshot, reader, role, run_kind)


def last_peak(role, run_kind, *, ledger=None, reader=None):
    """Use the last valid matching exit. Unavailable evidence keeps defaults."""
    import admission_memory as memory
    reader = memory.ScopeReader() if reader is None else reader
    ledger = Path(ledger or os.environ.get('ZESU_CANONICAL_LEDGER', memory.DEFAULT_LEDGER))
    try:
        with memory.ledger_transaction(ledger) as data:
            entries = copy.deepcopy(data.get('controller_exit_peaks', []))
            snapshot = copy.deepcopy(data)
        for entry in reversed(entries):
            if not isinstance(entry, dict) or entry.get('role') != role or entry.get('run_kind') != run_kind:
                continue
            try:
                value = _released(entry['receipt'], entry, snapshot, reader, role, run_kind)
                return entry['receipt'], value['memory_peak_bytes']
            except (AttributeError, KeyError, OSError, TypeError, ValueError):
                return None
    except (AttributeError, KeyError, OSError, TypeError, ValueError):
        pass
    return None


def _payload(command, context, runtime, reader, owner):
    if context['role'] == ROLES[0]:
        expected = context['command']
        path = Path(runtime['harness']['root']) / 'tools/block/harness/code/entry_chain_run.py'
        if (command != expected or len(command) != 5 or command[1] != '-B'
                or Path(command[2]) != path or command[3:] != ['--inside', runtime['job_output']]):
            raise ValueError('The controller client payload changed.')
    else:
        launcher = [word.replace('{workspace}', runtime['prepared_workspace'])
                    for word in runtime['mcp_argv']]
        boundary = launcher.index('--')
        if (len(command) < 10 or command[:2] != launcher[:2] or command[2] != 'enter'
                or command[8] != '--' or command[9:] != launcher[boundary+1:]):
            raise ValueError('The controller MCP payload changed.')
        pid, ticks, fd, device, inode = map(int, command[3:8])
        parent = {'pid': pid, 'startticks': ticks}
        reader.process(parent)
        info = (reader.proc / str(pid) / 'fd' / str(fd)).stat()
        if (reader.process(owner) != pid or not stat.S_ISFIFO(info.st_mode)
                or (info.st_dev, info.st_ino) != (device, inode)):
            raise ValueError('The controller MCP pipe owner changed.')


def begin(marker, command, *, ledger=None, reader=None, environment=None):
    """Authenticate the guard, live token, public runtime, and exact payload."""
    import admission_memory as memory
    reader = memory.ScopeReader() if reader is None else reader
    env = os.environ if environment is None else environment
    role = env.get('ZESU_CONTROLLER_ROLE')
    reference = {'path': env['ZESU_CONTROLLER_BOOKING_JSON'],
                 'sha256': env['ZESU_CONTROLLER_BOOKING_SHA256']}
    context, runtime = runtime_context(reference, reader)
    if (context['role'] != role or env.get('ZESU_CONTROLLER_RUN_KIND') != context['run_kind']
            or env.get('ZESU_CONTROLLER_AUTHORITY_SHA256') != context['booking']['authority']['sha256']):
        raise ValueError('The controller role environment changed.')
    if env.get('ZESU_MODULE_CLAIM_BYTES') != str(context['claim_bytes']):
        raise ValueError('The controller role environment changed its booking.')
    ledger = Path(ledger or env.get('ZESU_CANONICAL_LEDGER', memory.DEFAULT_LEDGER))
    key = memory.shell_key(marker)
    with memory.ledger_transaction(ledger) as data:
        snapshot = copy.deepcopy(data)
        owner = copy.deepcopy(data['shell_claim_owners'][key])
    actor = identity(os.getpid())
    attestation = owner['guard_attestation']
    if (actor != attestation['actor'] or owner['marker'] != str(Path(marker).absolute())
            or snapshot['fixed_claims'].get(key) != context['claim_bytes']
            or reader.claim(snapshot, key).get('verified') is not True):
        raise ValueError('The controller exit supervisor lacks its exact guarded actor.')
    argv = attestation['scope_exec_argv']
    position = argv.index('scope-exec')
    if argv[position+1:] != [str(marker), '--', *command]:
        raise ValueError('The guarded controller command changed.')
    reader.guard_source(owner['guard_source']['path'], owner['guard_source']['sha256'])
    _payload(command, context, runtime, reader, owner['owner'])
    from harness_commit import check
    check(runtime['harness'])
    roots = []
    for root_key, root_owner in snapshot.get('entry_pilot_outside_owners', {}).items():
        if not snapshot['fixed_claims'].get(root_key):
            continue
        try:
            if (reader.output(snapshot, root_key, root_owner, 'entry') == Path(runtime['job_output'])
                    and reader.ancestry(owner['owner']['pid'], root_owner)):
                roots.append((root_key, root_owner))
        except (KeyError, OSError, TypeError, ValueError):
            continue
    if len(roots) != 1:
        raise ValueError('The controller peak lacks its exact active canonical root.')
    root_key, root_owner = roots[0]
    root_args = reader.argv(root_owner)
    position = next(i for i, word in enumerate(root_args) if Path(word).name == 'entry_chain_run.py')
    configuration = read_bound({'path': root_args[position+1], 'sha256': root_args[position+2]})
    jobs = [job for job in configuration['jobs']
            if job['key'] == root_args[position+3] and job['output'] == runtime['job_output']]
    from scope_bookings import controller_only, run_kind
    if (len(jobs) != 1 or not controller_only(configuration, jobs[0])
            or run_kind(configuration, jobs[0]) != context['run_kind']
            or configuration['harness'] != runtime['harness']
            or configuration['job_controller'] != binding(root_args[position])):
        raise ValueError('The controller peak runtime differs from its canonical job.')
    limit = runtime['canonical_admission']['physical_fence_bytes']
    if type(limit) is not int or limit <= 0:
        raise ValueError('The controller physical fence is invalid.')
    fence(Path(attestation['leaf']['scope']), reader, limit)
    return {'ledger': ledger, 'reader': reader, 'physical_fence_bytes': limit, 'claim_key': key,
            'owner_record': owner, 'scope_actor': actor, 'scope': attestation['leaf'],
            'guard_source': owner['guard_source'], 'context': reference,
            'role': role, 'run_kind': context['run_kind'], 'root_claim_key': root_key, 'root_owner': root_owner}


def finish(start, payload, returncode):
    """Record the kernel peak after the payload and its process group ended."""
    import admission_memory as memory
    reader = start['reader']
    scope = start['scope']
    path = Path(scope['scope'])
    expected = (scope['device'], scope['inode'])
    if reader.directory(path) != expected:
        raise ValueError('The controller exit scope changed.')
    if reader.guard_source(start['guard_source']['path'], start['guard_source']['sha256']) != start['guard_source']:
        raise ValueError('The controller exit guard identity changed.')
    fence(path, reader, start['physical_fence_bytes'])
    peak = int((path/'memory.peak').read_text())
    fence(path, reader, start['physical_fence_bytes'])
    if peak <= 0 or reader.directory(path) != expected:
        raise ValueError('The controller exit peak is unavailable.')
    row = {name: start[name] for name in ('claim_key', 'owner_record', 'scope_actor',
            'scope', 'guard_source', 'context', 'role', 'run_kind', 'root_claim_key', 'root_owner', 'physical_fence_bytes')}
    row.update(schema=SCHEMA, payload_actor=payload, returncode=returncode,
               memory_peak_bytes=peak, payload_process_group_closed=True,
               finished_ns=time.time_ns(), qualification='Guarded role scope at payload exit; includes the supervisor.')
    if 'staging_registry' in start:
        row['staging_registry'] = start['staging_registry']
    destination = start['ledger'].parent/'controller-exit-peaks'
    destination.mkdir(mode=0o700, exist_ok=True)
    output = destination/(uuid.uuid4().hex+'.json')
    with open(output, 'x', opener=lambda name, flags: os.open(name, flags, 0o600)) as stream:
        json.dump(row, stream, sort_keys=True);stream.write('\n');stream.flush();os.fsync(stream.fileno())
    reference = binding(output)
    with memory.ledger_transaction(start['ledger']) as data:
        if (data['shell_claim_owners'].get(start['claim_key']) != start['owner_record']
                or data['fixed_claims'].get(start['claim_key'], 0) <= 0
                or not memory.ended_process(reader, payload)
                or reader.directory(path) != expected):
            raise ValueError('The controller exit ownership changed before publication.')
        reader.process(start['scope_actor'])
        data.setdefault('controller_exit_peaks', []).append({
            'receipt': reference, 'file_identity': list(reader.file_identity(output.lstat())),
            'role': start['role'], 'run_kind': start['run_kind']})
        memory.write_ledger(start['ledger'], data)
    return reference


def _group_members(group):
    found = []
    for path in Path('/proc').iterdir():
        if not path.name.isdecimal():
            continue
        try:
            fields = (path/'stat').read_text().rsplit(')', 1)[1].split()
            if int(fields[2]) == group and fields[0] not in ('Z', 'X', 'x'):
                found.append(int(path.name))
        except (OSError, ValueError, IndexError):
            continue
    return found


def run_payload(command, *, on_exit):
    """Preserve stdio and status. Reserve the child PID through group cleanup."""
    child = None
    pending = []
    def forward(number, frame):
        pending.append(number)
        if child is not None:
            try: os.killpg(child.pid, number)
            except ProcessLookupError: pass
    old = {number: signal.signal(number, forward)
           for number in (signal.SIGTERM, signal.SIGINT, signal.SIGHUP)}
    try:
        child = subprocess.Popen(command, start_new_session=True)
        actor = identity(child.pid)
        for number in pending:
            try: os.killpg(child.pid, number)
            except ProcessLookupError: pass
        os.waitid(os.P_PID, child.pid, os.WEXITED | os.WNOWAIT)
        closed = True
        try:
            os.killpg(child.pid, signal.SIGTERM)
            deadline = time.monotonic()+1
            while _group_members(child.pid) and time.monotonic() < deadline:
                time.sleep(.01)
            if _group_members(child.pid):
                os.killpg(child.pid, signal.SIGKILL)
                deadline = time.monotonic()+1
                while _group_members(child.pid) and time.monotonic() < deadline:
                    time.sleep(.01)
            if _group_members(child.pid):
                closed = False
        except OSError:
            closed = False
        finally:
            code = child.wait()
        if closed:
            on_exit(actor, code)
        else:
            print('resource guard: controller exit peak unavailable: payload cleanup is incomplete', file=sys.stderr)
        return code if code >= 0 else 128-code
    finally:
        if child is not None and child.poll() is None:
            os.killpg(child.pid, signal.SIGKILL);child.wait()
        for number, handler in old.items():
            signal.signal(number, handler)


def supervise(marker, command):
    start = begin(marker, command)
    def record(actor, code):
        try:
            finish(start, actor, code)
        except (KeyError, OSError, TypeError, ValueError) as error:
            print('resource guard: controller exit peak unavailable: '+str(error), file=sys.stderr)
    return run_payload(command, on_exit=record)
