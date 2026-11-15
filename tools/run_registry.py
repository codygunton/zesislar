#!/usr/bin/env python3
"""Register runs and stop exact superseded process identities before replacement.

The registry is shared by all worktrees through Git's common directory. It
records lifecycle data only. The stock guard owns admission and reservations.
Child launchers inherit ZESU_RUN_ID and must register processes that systemd
starts outside the scheduler's process tree.

`launch` (or `tools/bg NAME CMD...`) starts a long job in its own systemd user
scope, outside the caller's process tree, and prints its run ID; `stop <id>`
stops it. The reaper writes every run that ended by a signal without a stop
to signal-deaths.jsonl in the store; `watchdog` posts new entries to STATUS.md.
"""

from __future__ import annotations

import argparse
import copy
from contextlib import contextmanager
import ctypes
import datetime
import fcntl
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import signal
import subprocess
import sys
import time
import uuid

REFRESH_SECONDS = 5.0
# A launched job must register within this interval; it is an event ceiling.
LAUNCH_SECONDS = 120.0
LAUNCH_REFUSED = 3
SIGNAL_DEATH_SCHEMA = 'zesu.signal-death.v1'
# A shell reports a child killed by one of these signals as exit status 128+N.
SIGNAL_EXIT_CODES = {128 + number: number for number in
                     (signal.SIGHUP, signal.SIGINT, signal.SIGKILL, signal.SIGTERM)}


def identity(pid, proc=Path('/proc')):
    try:
        fields = (proc / str(pid) / 'stat').read_text().rsplit(')', 1)[1].split()
    except (FileNotFoundError, ProcessLookupError):
        return None
    return {'pid': int(pid), 'startticks': int(fields[19]),
            'ppid': int(fields[1]), 'state': fields[0]}


def live(actor):
    current = identity(actor['pid'])
    return bool(current and current['startticks'] == actor['startticks']
                and current['state'] not in ('Z', 'X'))


def actor_key(actor):
    return actor['pid'], actor['startticks']


def open_pidfd(pid):
    native = getattr(os, 'pidfd_open', None)
    if native is not None:
        return native(pid)
    # Some pinned Python builds omit the Linux bindings. Use the same kernel
    # interface through glibc, never a PID-only signal fallback.
    function = ctypes.CDLL(None, use_errno=True).pidfd_open
    function.argtypes = (ctypes.c_int, ctypes.c_uint)
    function.restype = ctypes.c_int
    result = function(pid, 0)
    if result < 0:
        error = ctypes.get_errno()
        raise OSError(error, os.strerror(error))
    return result


def signal_pidfd(fd, value):
    native = getattr(signal, 'pidfd_send_signal', None)
    if native is not None:
        return native(fd, value)
    function = ctypes.CDLL(None, use_errno=True).pidfd_send_signal
    function.argtypes = (ctypes.c_int, ctypes.c_int, ctypes.c_void_p, ctypes.c_uint)
    function.restype = ctypes.c_int
    if function(fd, value, None, 0) < 0:
        error = ctypes.get_errno()
        raise OSError(error, os.strerror(error))


def descendants(actors):
    """Retain only exact live roots and descendants of those roots."""
    snapshot = {}
    for entry in Path('/proc').iterdir():
        if entry.name.isdecimal():
            try:
                record = identity(int(entry.name))
            except (OSError, ValueError, IndexError):
                continue
            if record:
                snapshot[record['pid']] = record
    found = {a['pid']: snapshot[a['pid']] for a in actors
             if a['pid'] in snapshot
             and snapshot[a['pid']]['startticks'] == a['startticks']}
    while True:
        added = {pid: row for pid, row in snapshot.items()
                 if row['ppid'] in found and pid not in found}
        if not added:
            return list(found.values())
        found.update(added)


def send_signal(actor, value):
    """Use pidfds so PID reuse cannot redirect a stop signal."""
    if not live(actor):
        return False
    try:
        fd = open_pidfd(actor['pid'])
    except ProcessLookupError:
        return False
    try:
        if not live(actor):
            return False
        try:
            signal_pidfd(fd, value)
        except ProcessLookupError:
            return False
        return True
    finally:
        os.close(fd)


def default_store():
    configured = os.environ.get('ZESU_RUN_REGISTRY')
    if configured:
        return Path(configured).resolve()
    common = subprocess.check_output(
        ['git', 'rev-parse', '--path-format=absolute', '--git-common-dir'],
        cwd=Path(__file__).resolve().parent, text=True).strip()
    return Path(common) / 'zesu-runs'


def default_fence_ledger():
    """The resource guard's fence-kill ledger (STATE_DIR and FENCE_KILLS in resource_guard.sh)."""
    state = os.environ.get('ZESU_GUARD_STATE') or os.path.join(
        os.environ.get('XDG_RUNTIME_DIR') or '/tmp', 'zesu-guard')
    return Path(state) / 'fence-kills.jsonl'


def utc_text(ns):
    return datetime.datetime.fromtimestamp(ns / 1e9, datetime.timezone.utc).strftime('%Y-%m-%dT%H:%M:%SZ')


def own_cgroup():
    try:
        return Path('/proc/self/cgroup').read_text().strip().split('::', 1)[1]
    except (OSError, IndexError):
        return None


def cgroup_oom_kills():
    """OOM kills in the caller's cgroup (memory.events counts its descendants too)."""
    group = own_cgroup()
    if group is None:
        return None
    try:
        for line in (Path('/sys/fs/cgroup') / group.lstrip('/') / 'memory.events').read_text().splitlines():
            key, value = line.split()
            if key == 'oom_kill':
                return int(value)
    except (OSError, ValueError):
        return None
    return None


def stop_unit(unit):
    """End what is left in a launched run's scope; never the caller's own scope."""
    group = own_cgroup() or ''
    if group.rstrip('/').endswith('/' + unit) or '/' + unit + '/' in group:
        print(f'run registry: {unit} holds the caller; its unit is left running.', file=sys.stderr)
        return
    systemctl = shutil.which('systemctl')
    if systemctl is None:
        return
    # The registry already ended the recorded actors; what remains left the
    # process tree, so it gets SIGKILL at once. A scope that already ended is
    # no longer loaded, and both commands then fail harmlessly.
    for action in (['kill', '--signal=SIGKILL'], ['stop']):
        subprocess.run([systemctl, '--user', *action, unit],
                       stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL, check=False)


def slug(text, limit=32):
    value = re.sub(r'[^A-Za-z0-9_.-]+', '-', text).strip('-.')[:limit].strip('-.')
    return value or 'run'


def default_owner():
    """COORD_AGENT, else the omp agent name (its session file), else the user ID."""
    if os.environ.get('COORD_AGENT'):
        return os.environ['COORD_AGENT']
    session = os.environ.get('PI_SESSION_FILE')
    return Path(session).stem if session else str(os.getuid())


def spawn_detached(command, cwd, log):
    """Start command in a new session whose parent is init, never the caller.

    In the omp bash tool `$$` is the shared harness PID, and a kill by parent
    PID reaches every child of it. The intermediate process exits at once, so
    the command is reparented. It inherits no descriptor of the caller except
    /dev/null and the log. Return the command's PID.
    """
    read_end, write_end = os.pipe()
    child = os.fork()
    if child == 0:
        try:
            os.close(read_end)
            os.setsid()
            grandchild = os.fork()
            if grandchild:
                os.write(write_end, str(grandchild).encode())
                os._exit(0)
            os.chdir(cwd)
            null = os.open(os.devnull, os.O_RDONLY)
            output = os.open(log, os.O_WRONLY | os.O_CREAT | os.O_APPEND, 0o644)
            os.dup2(null, 0)
            os.dup2(output, 1)
            os.dup2(output, 2)
            os.closerange(3, os.sysconf('SC_OPEN_MAX'))
            os.execv(command[0], command)
        except BaseException as error:
            try:
                os.write(2, f'run registry: launch failed: {error}\n'.encode())
            finally:
                os._exit(127)
    os.close(write_end)
    os.waitpid(child, 0)
    with os.fdopen(read_end) as stream:
        text = stream.read()
    if not text.isdecimal():
        raise ValueError('The detached launch did not start.')
    return int(text)


def launch(registry, args):
    """Start a long job in its own systemd user scope outside the caller's process tree."""
    import kill_scan
    command = args.command[1:] if args.command[:1] == ['--'] else args.command
    if not command:
        raise ValueError('The launch command is empty.')
    run_dir = Path(args.dir or os.getcwd()).resolve()
    if not run_dir.is_dir():
        raise ValueError(f'The run directory {run_dir} does not exist.')
    findings = kill_scan.scan_command(command, run_dir)
    if findings:
        print('run registry: launch refused: the command can kill jobs it does not own.', file=sys.stderr)
        for finding in findings:
            print(finding.message(), file=sys.stderr)
        return LAUNCH_REFUSED
    systemd_run = shutil.which('systemd-run')
    if systemd_run is None:
        raise ValueError('systemd-run is not available; the launcher needs a user scope.')
    owner = args.owner or default_owner()
    stamp = time.strftime('%Y%m%dT%H%M%SZ', time.gmtime())
    run_id = f'{slug(owner)}-{slug(args.name)}-{stamp}-{uuid.uuid4().hex[:6]}'
    unit = f'zesubg-{run_id}.scope'
    log = Path(args.log).resolve() if args.log else run_dir / f'{slug(args.name)}.log'
    scope = [systemd_run, '--user', '--scope', '--quiet', '--collect', f'--unit={unit}']
    details = ['--unit', unit, '--run-dir', str(run_dir), '--log', str(log), '--no-run-id-env']
    if args.memory:
        scope += ['-p', f'MemoryMax={args.memory}G', '-p', 'MemorySwapMax=0']
        details += ['--memory-gib', str(args.memory)]
    pid = spawn_detached(
        [*scope, '--', sys.executable, '-B', str(Path(__file__).resolve()), '--store', str(registry.directory),
         'run', '--id', run_id, '--kind', args.kind, '--owner', owner, *details, '--', *command],
        run_dir, log)
    deadline = time.monotonic() + LAUNCH_SECONDS
    while True:
        try:
            row = registry.read_run(run_id)
        except KeyError:
            row = None
        if row is not None and (row['jobs'] or row['status'] != 'running'):
            break
        started = identity(pid)
        if row is None and (started is None or started['state'] in ('Z', 'X')):
            raise ValueError(f'The launch ended before it registered; see {log}.')
        if time.monotonic() >= deadline:
            raise ValueError(f'The launch did not register within {LAUNCH_SECONDS:.0f} s; see {log}.')
        time.sleep(0.05)
    job = row['jobs'][0]['pid'] if row['jobs'] else None
    print(run_id)
    print(f'run registry: launched {run_id}: unit {unit}, scheduler {pid}, job {job}, status {row["status"]}, '
          f'log {log}. Stop: tools/run_registry.py stop {run_id}', file=sys.stderr)
    return 0


def watchdog(registry, status):
    """Reap, then append new signal-death entries to STATUS.md.

    The first pass only records the ledger position, so entries reaped from
    history before the watchdog ran are kept in the ledger but not posted.
    """
    registry.reap()
    cursor = registry.directory / 'signal-deaths.posted'
    with registry.lock('watchdog'):
        lines = []
        if registry.signal_ledger.exists():
            with registry.signal_ledger.open() as stream:
                fcntl.flock(stream, fcntl.LOCK_SH)
                lines = [line for line in stream.read().splitlines() if line.strip()]
        if not cursor.exists():
            Registry.atomic_write(cursor, {'posted': len(lines)})
            return []
        posted = json.loads(cursor.read_text())['posted']
        now = time.strftime('%Y-%m-%dT%H:%MZ', time.gmtime())
        messages = []
        for line in lines[posted:]:
            entry = json.loads(line)
            ended = entry['signal_name'] or 'an unrecorded signal'
            fence = f" ({entry['fence_unit']})" if entry.get('fence_unit') else ''
            messages.append(
                f"- {now} run-watchdog: run {entry['run_id']} (owner {entry['owner']}, kind {entry['kind']}, "
                f"unit {entry['unit'] or 'none'}) ended by {ended} at {entry['utc']} without a registry stop "
                f"({entry['evidence']}); cause: {entry['cause']}{fence}. Ledger: {registry.signal_ledger}.")
        if messages:
            with Path(status).open('a') as stream:
                stream.write(''.join(message + '\n' for message in messages))
        Registry.atomic_write(cursor, {'posted': len(lines)})
        return messages


class Registry:
    def __init__(self, directory, fence_ledger=None):
        self.directory = Path(directory).resolve()
        self.directory.mkdir(parents=True, exist_ok=True)
        self.path = self.directory / 'runs.json'
        self.fence_ledger = Path(fence_ledger) if fence_ledger else default_fence_ledger()

    @contextmanager
    def lock(self, name='state'):
        with (self.directory / (name + '.lock')).open('a') as handle:
            fcntl.flock(handle, fcntl.LOCK_EX)
            yield

    def read(self):
        with self.lock():
            data = self.header()
            if data['schema'] == 'zesu.run-registry.v2':
                rows = []
                for path in sorted((self.directory / 'runs.d').glob('*.json')):
                    row = self.read_file(path)
                    if self.row_path(row['id']) != path:
                        raise ValueError('A run record has an invalid ID.')
                    rows.append(row)
                return {'schema': data['schema'], 'runs': {r['id']: r for r in rows}}
            return data

    @staticmethod
    def read_file(path):
        return json.loads(path.read_text())

    def header(self):
        if not self.path.exists():
            return {'schema': 'zesu.run-registry.v1', 'runs': {}}
        result = self.read_file(self.path)
        if result.get('schema') not in ('zesu.run-registry.v1', 'zesu.run-registry.v2'):
            raise ValueError('The run registry schema is unsupported.')
        if (result['schema'] == 'zesu.run-registry.v2'
                and not (self.directory / 'runs.d').is_dir()):
            raise ValueError('The per-run store directory is missing.')
        return result

    @staticmethod
    def sync_directory(path):
        descriptor = os.open(path, os.O_RDONLY | os.O_DIRECTORY)
        try:
            os.fsync(descriptor)
        finally:
            os.close(descriptor)

    @staticmethod
    def atomic_write(path, value):
        temporary = path.parent / ('.runs-' + uuid.uuid4().hex)
        try:
            with temporary.open('x') as handle:
                json.dump(value, handle, indent=2)
                handle.write('\n')
                handle.flush()
                os.fsync(handle.fileno())
            os.replace(temporary, path)
            Registry.sync_directory(path.parent)
        finally:
            temporary.unlink(missing_ok=True)

    def write(self, value):
        if self.header()['schema'] != 'zesu.run-registry.v1':
            raise ValueError('The per-run store refuses a bulk write.')
        self.atomic_write(self.path, value)

    def row_path(self, run_id):
        return self.directory / 'runs.d' / (hashlib.sha256(run_id.encode()).hexdigest() + '.json')

    def load_row(self, data, run_id):
        if data['schema'] == 'zesu.run-registry.v1':
            return data['runs'][run_id]
        try:
            row = self.read_file(self.row_path(run_id))
        except FileNotFoundError:
            raise KeyError(run_id) from None
        if row['id'] != run_id:
            raise ValueError('The run record ID does not match its file.')
        return row

    def read_run(self, run_id):
        with self.lock():
            return self.read_run_unlocked(run_id)

    def read_run_unlocked(self, run_id):
        # Signal handlers can interrupt a writer that holds state.lock.
        # Each file replacement is atomic; migration refuses live actors.
        return self.load_row(self.header(), run_id)

    def contains(self, run_id):
        try:
            self.read_run(run_id)
        except KeyError:
            return False
        return True

    def save_row(self, data, row):
        if data['schema'] == 'zesu.run-registry.v1':
            data['runs'][row['id']] = row
            self.write(data)
        else:
            self.atomic_write(self.row_path(row['id']), row)

    def migrate(self):
        """Opt in only after every actor and claim closes; old writers then refuse."""
        with self.lock('transition'), self.lock():
            data = self.header()
            if data['schema'] != 'zesu.run-registry.v1':
                raise ValueError('The store already uses per-run files.')
            for run_id, row in data['runs'].items():
                if row['id'] != run_id:
                    raise ValueError('The run record ID does not match its key.')
                if (any(live(a) for a in [row['scheduler']] + row['jobs'])
                        or any(not c['released'] for c in row['claims'].values())):
                    raise ValueError('Migration requires closed actors and released claims.')
            target = self.directory / 'runs.d'
            if target.exists():
                raise ValueError('An existing per-run directory blocks migration.')
            staging = self.directory / ('.migration-' + uuid.uuid4().hex)
            staging.mkdir()
            # A failed migration leaves v1 authoritative. Retain partial files
            # for inspection; never adopt them during a later attempt.
            for row in data['runs'].values():
                self.atomic_write(staging / self.row_path(row['id']).name, row)
            backup = self.directory / ('runs.v1-' + uuid.uuid4().hex + '.json')
            self.atomic_write(backup, data)
            os.rename(staging, target)
            self.sync_directory(self.directory)
            self.atomic_write(self.path, {'schema': 'zesu.run-registry.v2',
                                         'legacy_snapshot': backup.name})

    def update(self, run_id, operation):
        with self.lock():
            data = self.header()
            row = self.load_row(data, run_id)
            previous = copy.deepcopy(row)
            operation(row)
            if row != previous:
                self.save_row(data, row)
            return row

    def register(self, run_id, kind, owner, scheduler, command, details=None):
        if not run_id or not kind or not owner:
            raise ValueError('The run needs an ID, kind, and owner.')
        if not live(scheduler):
            raise ValueError('The scheduler identity is not live.')
        self.reap()
        with self.lock():
            data = self.header()
            try:
                self.load_row(data, run_id)
            except KeyError:
                pass
            else:
                raise ValueError('The run ID already exists. Use a fresh run ID.')
            row = {
                'id': run_id, 'kind': kind, 'owner': owner,
                'scheduler': scheduler, 'jobs': [], 'claims': {},
                'command': command, 'registered_ns': time.time_ns(),
                'status': 'running', **(details or {})}
            self.save_row(data, row)

    def add_job(self, run_id, actor):
        if not live(actor):
            raise ValueError('The job identity is not live.')
        def append(row):
            if row['status'] != 'running':
                raise ValueError('The run does not accept more jobs.')
            if actor_key(actor) not in {actor_key(a) for a in row['jobs']}:
                row['jobs'].append(actor)
        self.update(run_id, append)

    @staticmethod
    def refresh_row(row):
        actors = descendants([row['scheduler']] + row['jobs'])
        retained = {actor_key(a): a for a in row['jobs'] if live(a)}
        for actor in actors:
            if actor_key(actor) != actor_key(row['scheduler']):
                # Process state changes do not change an actor identity.
                previous = retained.get(actor_key(actor))
                if previous is None or previous['ppid'] != actor['ppid']:
                    retained[actor_key(actor)] = actor
        row['jobs'] = list(retained.values())

    def refresh(self, run_id):
        while True:
            with self.lock():
                previous = copy.deepcopy(self.load_row(self.header(), run_id))
            refreshed = copy.deepcopy(previous)
            self.refresh_row(refreshed)
            with self.lock():
                data = self.header()
                if self.load_row(data, run_id) != previous:
                    # Discovery must not overwrite a concurrent registry update.
                    continue
                if refreshed != previous:
                    self.save_row(data, refreshed)
                return refreshed

    def add_claim(self, run_id, claim_id, command):
        if not claim_id or not command:
            raise ValueError('The claim needs an ID and a release command.')
        def append(row):
            if row['status'] != 'running' or claim_id in row['claims']:
                raise ValueError('The run refuses this claim registration.')
            row['claims'][claim_id] = {'release_command': command, 'released': False}
        self.update(run_id, append)

    def claim_released(self, run_id, claim_id):
        def mark(row):
            row['claims'][claim_id]['released'] = True
        self.update(run_id, mark)

    def release_claims(self, run_id):
        suffix = hashlib.sha256(run_id.encode()).hexdigest()
        with self.lock('release-' + suffix):
            row = self.read_run(run_id)
            if any(live(a) for a in row['jobs']):
                raise ValueError('The run still has live jobs. Its claims remain reserved.')
            for name, claim in row['claims'].items():
                if not claim['released']:
                    subprocess.run(claim['release_command'], check=True)
                    self.claim_released(run_id, name)

    def stop(self, run_id, *, grace=5.0):
        """Stop the scheduler, close its jobs, release registered claims, then stop its unit.

        A launched run's systemd scope can hold processes that left the
        scheduler's process tree; stopping the unit ends them too.
        """
        units = []
        try:
            self.stop_actors(run_id, grace, units)
        finally:
            for unit in units:
                stop_unit(unit)

    def stop_actors(self, run_id, grace, units):
        frozen = {}
        try:
            # Acquire state before freezing any actor. Otherwise an actor can
            # keep this lock while stopped and prevent discovery or cleanup.
            with self.lock():
                data = self.header()
                row = self.load_row(data, run_id)
                scheduler = row['scheduler']
                caller = actor_key(identity(os.getpid()))
                if actor_key(scheduler) == caller:
                    raise ValueError('The registry cannot stop its own caller.')
                # A caller inside the run would freeze itself while it holds
                # this lock. run_wall_stop.py stops such a run from outside.
                if caller in {actor_key(a) for a in descendants([scheduler] + row['jobs'])}:
                    raise ValueError('The registry cannot stop a run that contains its caller.')
                row.update(status='stopping', stop_requested_ns=time.time_ns(),
                           stop_requested_by=os.getpid())
                if row.get('unit'):
                    units.append(row['unit'])
                freeze_deadline = time.monotonic() + grace
                while True:
                    self.refresh_row(row)
                    actors = [scheduler] + row['jobs']
                    fresh = [a for a in actors if actor_key(a) not in frozen and live(a)]
                    for actor in fresh:
                        if send_signal(actor, signal.SIGSTOP):
                            frozen[actor_key(actor)] = actor
                    # A stop signal can return before the actor stops. Wait
                    # for stopped identities before the final descendant scan.
                    # The launching shell of a scheduler can resume it at once
                    # (agent background shells do). A scheduler launches no
                    # actor after its command starts, so once a job exists
                    # the freeze waits only for the jobs; the scheduler still
                    # receives SIGTERM and SIGKILL below.
                    launched = bool(row['jobs'])
                    pending = []
                    for actor in actors:
                        if launched and actor_key(actor) == actor_key(scheduler):
                            continue
                        current = identity(actor['pid'])
                        if (current and current['startticks'] == actor['startticks']
                                and current['state'] not in ('T', 't', 'Z', 'X')):
                            pending.append(actor)
                    if not fresh and not pending:
                        break
                    if time.monotonic() >= freeze_deadline:
                        row.update(status='stop_failed', all_actors_closed=False,
                                   stop_error='Actors did not stop within the grace interval.',
                                   stop_pending=pending)
                        self.save_row(data, row)
                        raise ValueError(row['stop_error'])
                    if pending:
                        time.sleep(0.01)
                self.save_row(data, row)
            # Closing wrappers and release callbacks need state.lock. Do not
            # retain it while resuming actors or waiting for their exits.
            actors = row['jobs'] + [scheduler]
            for actor in actors:
                send_signal(actor, signal.SIGTERM)
                send_signal(actor, signal.SIGCONT)
            deadline = time.monotonic() + grace
            while any(live(a) for a in actors) and time.monotonic() < deadline:
                time.sleep(0.05)
            for actor in actors:
                send_signal(actor, signal.SIGKILL)
            deadline = time.monotonic() + grace
            while any(live(a) for a in actors) and time.monotonic() < deadline:
                time.sleep(0.05)
            if any(live(a) for a in actors):
                raise ValueError('The superseded run still has live actors.')
            self.update(run_id, lambda r: r.update(
                status='stopped', closed_ns=time.time_ns(), all_actors_closed=True))
            self.release_claims(run_id)
        except BaseException:
            for actor in frozen.values():
                send_signal(actor, signal.SIGCONT)
            raise

    def reap(self):
        """Close dead orphans and record runs that ended by a signal without a stop."""
        rows = list(self.read()['runs'].values())
        self.reap_orphans(rows)
        return self.reap_signal_deaths(rows)

    def reap_orphans(self, rows):
        """Release claims of children_live runs whose exact actors all ended."""
        for row in rows:
            if row['status'] != 'children_live':
                continue
            if any(live(a) for a in [row['scheduler']] + row['jobs']):
                continue
            try:
                self.release_claims(row['id'])
            except (OSError, ValueError, subprocess.CalledProcessError) as error:
                # The claim stays reserved; a later pass retries the release.
                print(f"run registry: orphan {row['id']} keeps its claims: {error}",
                      file=sys.stderr)
                continue
            def close(current):
                if current['status'] == 'children_live':
                    current.update(status='closed', closed_ns=time.time_ns(),
                                   all_actors_closed=True)
            self.update(row['id'], close)

    @property
    def signal_ledger(self):
        return self.directory / 'signal-deaths.jsonl'

    @staticmethod
    def death_signal(row):
        """Return (signal or None, evidence) for a run that ended by a signal without a stop.

        A stop through this registry records stop_requested_ns and leaves the
        run stopping, stopped, or stop_failed; such a run never qualifies. A
        running row whose exact actors all ended lost its scheduler before the
        scheduler could record an exit, which only a signal does.
        """
        if row.get('signal_death_ns') or row.get('stop_requested_ns'):
            return None
        if row['status'] == 'running':
            if any(live(a) for a in [row['scheduler']] + row['jobs']):
                return None
            return None, 'scheduler ended without a record'
        if row['status'] not in ('completed', 'failed'):
            return None
        if row.get('signal'):
            return row['signal'], 'signal'
        code = row.get('exit_code')
        if isinstance(code, int) and code < 0:
            return -code, 'signal'
        if code in SIGNAL_EXIT_CODES:
            return SIGNAL_EXIT_CODES[code], 'exit status'
        return None

    def fence_kills(self):
        """Rows of the resource guard's fence-kill ledger (resource_guard.sh FENCE_KILLS)."""
        try:
            lines = self.fence_ledger.read_text().splitlines()
        except OSError:
            return []
        rows = []
        for line in lines:
            try:
                row = json.loads(line)
            except ValueError:
                continue
            if isinstance(row, dict):
                rows.append(row)
        return rows

    @staticmethod
    def death_cause(row, fences):
        """Label a signal death 'memory fence' when a memory kill explains it."""
        if row.get('oom_kills'):
            return ('memory fence' if row.get('memory_gib') else 'oom kill'), row.get('unit')
        for fence in fences:
            if fence.get('run_id') == row['id'] or (row.get('unit') and fence.get('unit') == row['unit']):
                return 'memory fence', fence.get('unit')
        return 'unknown', None

    def reap_signal_deaths(self, rows):
        """Append one ledger entry per run that ended by a signal without a stop."""
        candidates = [row for row in rows if self.death_signal(row)]
        if not candidates:
            return []
        fences = self.fence_kills()
        entries = []
        for candidate in candidates:
            def mark(row):
                found = self.death_signal(row)
                if found is None:
                    return
                number, evidence = found
                cause, fence_unit = self.death_cause(row, fences)
                ended_ns = row.get('closed_ns') or time.time_ns()
                entry = {
                    'schema': SIGNAL_DEATH_SCHEMA, 'run_id': row['id'], 'owner': row['owner'],
                    'kind': row['kind'], 'unit': row.get('unit'), 'run_dir': row.get('run_dir'),
                    'command': row.get('command'), 'signal': number,
                    'signal_name': signal.Signals(number).name if number else None,
                    'evidence': evidence, 'exit_code': row.get('exit_code'),
                    'utc': utc_text(ended_ns), 'cause': cause, 'fence_unit': fence_unit}
                with self.signal_ledger.open('a') as stream:
                    fcntl.flock(stream, fcntl.LOCK_EX)
                    stream.write(json.dumps(entry, sort_keys=True) + '\n')
                row['signal_death_ns'] = time.time_ns()
                entries.append(entry)
            try:
                self.update(candidate['id'], mark)
            except KeyError:
                continue
        return entries

    def active(self):
        self.reap()
        rows = []
        for row in self.read()['runs'].values():
            actors = [row['scheduler']] + row['jobs']
            pending = [name for name, c in row['claims'].items() if not c['released']]
            living = [a for a in actors if live(a)]
            if living or pending:
                rows.append({**row, 'live_actors': living, 'pending_claims': pending})
        return rows


def run_command(registry, args):
    command = args.command
    if command[:1] == ['--']:
        command = command[1:]
    if not command:
        raise ValueError('The run command is empty.')
    owner = args.owner or os.environ.get('COORD_AGENT') or str(os.getuid())
    run_id = args.id or f'{args.kind}-{time.time_ns()}-{os.getpid()}'
    interrupted = []
    actor = None
    process = None
    command_ended = False
    registered = False
    def interrupt(signum, _frame):
        interrupted.append(signum)
        if registered and actor is not None:
            for current in descendants([actor]):
                send_signal(current, signum)
    previous = {number: signal.signal(number, interrupt)
                for number in (signal.SIGTERM, signal.SIGINT, signal.SIGHUP)}
    try:
        # Install cancellation before a child can exist. The handler records a
        # launch-time interruption until the exact child identity is available.
        with registry.lock('transition'):
            if registry.contains(run_id):
                raise ValueError('The run ID already exists. Use a fresh run ID.')
            for old_id in args.supersedes:
                old = registry.read_run(old_id)
                if old['owner'] != owner or old['kind'] != args.kind:
                    raise ValueError('A replacement must keep the old owner and kind.')
                registry.stop(old_id)
            details = {key: value for key, value in (
                ('unit', getattr(args, 'unit', None)), ('run_dir', getattr(args, 'run_dir', None)),
                ('log', getattr(args, 'log', None)), ('memory_gib', getattr(args, 'memory_gib', None)))
                if value is not None}
            registry.register(run_id, args.kind, owner, identity(os.getpid()), command, details)
            if getattr(args, 'no_run_id_env', False):
                # A launched job is a top-level run: the guard batches it starts
                # register their own runs, as they would from a terminal.
                environment = {key: value for key, value in os.environ.items()
                               if key not in ('ZESU_RUN_ID', 'ZESU_RUN_REGISTRY')}
                environment['ZESU_BG_RUN_ID'] = run_id
            else:
                environment = dict(os.environ, ZESU_RUN_ID=run_id,
                                   ZESU_RUN_REGISTRY=str(registry.directory))
            try:
                if not interrupted:
                    process = subprocess.Popen(command, env=environment, start_new_session=True)
                    actor = identity(process.pid)
                    if actor and live(actor):
                        registry.add_job(run_id, actor)
                    registered = True
            except BaseException:
                registry.update(run_id, lambda row: row.update(status='launch_failed'))
                raise
        if interrupted and actor is not None:
            for current in descendants([actor]):
                send_signal(current, interrupted[0])
        next_refresh = 0.0
        while process is not None and process.poll() is None:
            now = time.monotonic()
            if now >= next_refresh:
                registry.refresh(run_id)
                next_refresh = time.monotonic() + REFRESH_SECONDS
            time.sleep(0.1)
        status = process.wait() if process is not None else 128 + interrupted[0]
        command_ended = True
        row = registry.refresh(run_id)
        if row['status'] != 'stopping':
            if any(live(current) for current in row['jobs']):
                registry.update(run_id, lambda row: row.update(status='children_live'))
                raise ValueError('The command ended with live jobs. Its claims remain reserved.')
            registry.release_claims(run_id)
            ended = {'status': 'completed' if status == 0 else 'failed', 'exit_code': status,
                     'closed_ns': time.time_ns(), 'all_actors_closed': True}
            if interrupted or status < 0:
                ended['signal'] = interrupted[0] if interrupted else -status
            oom_kills = cgroup_oom_kills() if details.get('unit') else None
            if oom_kills:
                ended['oom_kills'] = oom_kills
            registry.update(run_id, lambda row: row.update(ended))
        return 128 + interrupted[0] if interrupted else (128 - status if status < 0 else status)
    finally:
        if process is not None and not command_ended and actor is not None and process.poll() is None:
            for current in descendants([actor]):send_signal(current, signal.SIGTERM)
            process.wait(timeout=60)
        for signum, handler in previous.items():
            signal.signal(signum, handler)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--store', type=Path)
    commands = parser.add_subparsers(dest='action', required=True)
    run = commands.add_parser('run')
    run.add_argument('--id')
    run.add_argument('--kind', required=True)
    run.add_argument('--owner')
    run.add_argument('--supersedes', action='append', default=[])
    run.add_argument('--unit', help='The systemd unit that holds the run (set by launch).')
    run.add_argument('--run-dir')
    run.add_argument('--log')
    run.add_argument('--memory-gib', type=int)
    run.add_argument('--no-run-id-env', action='store_true',
                     help='Do not export ZESU_RUN_ID; the command registers its own runs.')
    run.add_argument('command', nargs=argparse.REMAINDER)
    start = commands.add_parser('launch', help='Start a long job in its own user scope (tools/bg).')
    start.add_argument('--name', required=True)
    start.add_argument('--owner')
    start.add_argument('--kind', default='bg')
    start.add_argument('--dir', help='Run directory and working directory (default: the current one).')
    start.add_argument('--log', help='Output file (default: RUN_DIR/NAME.log, appended).')
    start.add_argument('--memory', type=int, choices=range(1, 1000), metavar='GIB',
                       help='Scope MemoryMax in GiB, with swap off.')
    start.add_argument('command', nargs=argparse.REMAINDER)
    commands.add_parser('reap', help='Record runs that ended by a signal without a stop.')
    guard = commands.add_parser('watchdog', help='Reap, then post new signal deaths to STATUS.md.')
    guard.add_argument('--status', type=Path, required=True)
    listing = commands.add_parser('list')
    listing.add_argument('--active', action='store_true')
    listing.add_argument('--json', action='store_true')
    commands.add_parser('migrate-per-run', help='Opt in after all actors and claims close.')
    begin = commands.add_parser('begin')
    begin.add_argument('--id', required=True)
    begin.add_argument('--kind', required=True)
    begin.add_argument('--owner', required=True)
    begin.add_argument('--pid', type=int, required=True)
    begin.add_argument('--startticks', type=int, required=True)
    begin.add_argument('--supersedes', action='append', default=[])
    for name in ('register-job', 'register-claim', 'claim-released', 'finish', 'stop'):
        sub = commands.add_parser(name)
        sub.add_argument('--run-id', default=os.environ.get('ZESU_RUN_ID'))
        if name == 'register-job':
            sub.add_argument('--pid', type=int, required=True)
            sub.add_argument('--startticks', type=int, required=True)
        elif name in ('register-claim', 'claim-released'):
            sub.add_argument('--claim-id', required=True)
            if name == 'register-claim':
                sub.add_argument('command', nargs=argparse.REMAINDER)
        elif name == 'finish':
            sub.add_argument('--status', required=True)
        elif name == 'stop':
            sub.add_argument('id', nargs='?', help='The run ID (same as --run-id).')
    args = parser.parse_args()
    registry = Registry(args.store or default_store())
    if args.action == 'migrate-per-run':
        if args.store is None:
            raise ValueError('Migration requires an explicit --store path.')
        registry.migrate()
        return 0
    if args.action == 'run':
        return run_command(registry, args)
    if args.action == 'launch':
        return launch(registry, args)
    if args.action == 'reap':
        for entry in registry.reap():
            print(json.dumps(entry, sort_keys=True))
        return 0
    if args.action == 'watchdog':
        for message in watchdog(registry, args.status):
            print(message)
        return 0
    if args.action == 'begin':
        actor = identity(args.pid)
        if actor is None or actor['startticks'] != args.startticks:
            raise ValueError('The scheduler PID and start ticks do not match.')
        with registry.lock('transition'):
            if registry.contains(args.id):
                raise ValueError('The run ID already exists. Use a fresh run ID.')
            for old_id in args.supersedes:
                old = registry.read_run(old_id)
                if old['owner'] != args.owner or old['kind'] != args.kind:
                    raise ValueError('A replacement must keep the old owner and kind.')
                registry.stop(old_id)
            registry.register(args.id, args.kind, args.owner, actor, [])
        return 0
    if args.action == 'list':
        rows = registry.active() if args.active else list(registry.read()['runs'].values())
        if args.json:
            print(json.dumps(rows, indent=2))
        else:
            for row in rows:
                print(f"{row['id']} {row['kind']} {row['owner']} {row['status']} "
                      f"scheduler={row['scheduler']['pid']}:{row['scheduler']['startticks']} "
                      f"jobs={len(row['jobs'])}" + (f" unit={row['unit']}" if row.get('unit') else ''))
        return 0
    if args.action == 'stop' and args.id:
        args.run_id = args.id
    if not args.run_id:
        raise ValueError('The operation needs a run ID.')
    if args.action == 'register-job':
        actor = identity(args.pid)
        if actor is None or actor['startticks'] != args.startticks:
            raise ValueError('The job PID and start ticks do not match.')
        registry.add_job(args.run_id, actor)
    elif args.action == 'register-claim':
        command = args.command[1:] if args.command[:1] == ['--'] else args.command
        registry.add_claim(args.run_id, args.claim_id, command)
    elif args.action == 'claim-released':
        registry.claim_released(args.run_id, args.claim_id)
    elif args.action == 'stop':
        with registry.lock('transition'):
            registry.stop(args.run_id)
    elif args.action == 'finish':
        row = registry.refresh(args.run_id)
        if live(row['scheduler']) or any(live(a) for a in row['jobs']):
            raise ValueError('The run still has live actors.')
        registry.release_claims(args.run_id)
        registry.update(args.run_id, lambda r: r.update(
            status=args.status, closed_ns=time.time_ns(), all_actors_closed=True))
    return 0


if __name__ == '__main__':
    try:
        raise SystemExit(main())
    except (OSError, ValueError, KeyError, subprocess.CalledProcessError) as error:
        print(f'run registry: {error}', file=sys.stderr)
        raise SystemExit(2)
