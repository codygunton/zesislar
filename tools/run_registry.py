#!/usr/bin/env python3
"""Register runs and stop exact superseded process identities before replacement.

The registry is shared by all worktrees through Git's common directory. It
records lifecycle data only. The stock guard owns admission and reservations.
Child launchers inherit ZESU_RUN_ID and must register processes that systemd
starts outside the scheduler's process tree.
"""

from __future__ import annotations

import argparse
import copy
from contextlib import contextmanager
import ctypes
import fcntl
import hashlib
import json
import os
from pathlib import Path
import signal
import subprocess
import sys
import time
import uuid

REFRESH_SECONDS = 3.0


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


class Registry:
    def __init__(self, directory):
        self.directory = Path(directory).resolve()
        self.directory.mkdir(parents=True, exist_ok=True)
        self.path = self.directory / 'runs.json'

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

    def register(self, run_id, kind, owner, scheduler, command):
        if not run_id or not kind or not owner:
            raise ValueError('The run needs an ID, kind, and owner.')
        if not live(scheduler):
            raise ValueError('The scheduler identity is not live.')
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
                'status': 'running'}
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
        retained = {actor_key(a): a for a in row['jobs']}
        for actor in actors:
            if actor_key(actor) != actor_key(row['scheduler']):
                # Process state changes do not change an actor identity.
                previous = retained.get(actor_key(actor))
                if previous is None or previous['ppid'] != actor['ppid']:
                    retained[actor_key(actor)] = actor
        row['jobs'] = list(retained.values())

    def refresh(self, run_id):
        return self.update(run_id, self.refresh_row)

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
        """Stop the scheduler, close its jobs, then release registered claims."""
        frozen = {}
        try:
            # Acquire state before freezing any actor. Otherwise an actor can
            # keep this lock while stopped and prevent discovery or cleanup.
            with self.lock():
                data = self.header()
                row = self.load_row(data, run_id)
                scheduler = row['scheduler']
                if actor_key(scheduler) == actor_key(identity(os.getpid())):
                    raise ValueError('The registry cannot stop its own caller.')
                row['status'] = 'stopping'
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
                    pending = []
                    for actor in actors:
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

    def active(self):
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
            registry.register(run_id, args.kind, owner, identity(os.getpid()), command)
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
            registry.update(run_id, lambda row: row.update(
                status='completed' if status == 0 else 'failed',
                exit_code=status, closed_ns=time.time_ns(), all_actors_closed=True))
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
    run.add_argument('command', nargs=argparse.REMAINDER)
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
    args = parser.parse_args()
    registry = Registry(args.store or default_store())
    if args.action == 'migrate-per-run':
        if args.store is None:
            raise ValueError('Migration requires an explicit --store path.')
        registry.migrate()
        return 0
    if args.action == 'run':
        return run_command(registry, args)
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
                      f"jobs={len(row['jobs'])}")
        return 0
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
