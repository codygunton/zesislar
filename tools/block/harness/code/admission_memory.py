"""Account reservations and verified live usage against both memory limits.

Only an exact owner token, batch identity, and live kernel membership can earn
memory.current credit. Missing evidence retains the complete reservation.
"""
import json
import fcntl
import hashlib
import tempfile
from contextlib import contextmanager
import os
from pathlib import Path
import re
import stat

GIB = 1024 ** 3
HEADROOM_BYTES = 20 * GIB
SLICE_MAX_BYTES = 175 * GIB
CGROUP_ROOT = Path('/sys/fs/cgroup')
PROC = Path('/proc')


def integer(value, label):
    if type(value) is not int or value < 0:
        raise ValueError('Invalid nonnegative memory amount: ' + label)
    return value


def evaluate(claims, new_bytes, available_bytes, *, observations=None, new_observation=None,
             slice_max_bytes=None, headroom_bytes=HEADROOM_BYTES):
    """Evaluate both inequalities. Observations come from ScopeReader only."""
    for key, amount in claims.items():
        integer(amount, key)
    integer(new_bytes, 'new claim')
    if new_observation is not None:
        if '__new_claim__' in claims:
            raise ValueError('The new claim key collides.')
        combined = dict(claims, __new_claim__=new_bytes)
        observed = dict(observations or {}, __new_claim__=new_observation)
        result = evaluate(combined, 0, available_bytes, observations=observed,
                          slice_max_bytes=slice_max_bytes, headroom_bytes=headroom_bytes)
        result['new_claim_bytes'] = new_bytes
        return result
    integer(available_bytes, 'available memory')
    integer(headroom_bytes, 'fixed headroom')
    if slice_max_bytes is None:
        slice_max_bytes = ScopeReader().slice_max()
    integer(slice_max_bytes, 'verified slice maximum')
    rows = {}
    observations = observations or {}
    for key, amount in claims.items():
        row = observations.get(key, {})
        if not amount and not (row.get('verified') is True and row.get('live_bytes', 0)):
            continue
        live = row.get('live_bytes', 0) if row.get('verified') is True else 0
        integer(live, 'verified live memory')
        rows[key] = dict(row, claim_bytes=amount, accounted_bytes=max(amount, live),
                         credited_bytes=min(amount, live),
                         reason=row.get('reason', 'unverified scope'))
    ambiguous = set()
    candidates = [key for key, row in rows.items() if row.get('verified') is True]
    for index, key in enumerate(candidates):
        left = rows[key]
        for other in candidates[index + 1:]:
            right = rows[other]
            a, b = Path(left['scope']), Path(right['scope'])
            same = a == b and (left['device'], left['inode']) == (right['device'], right['inode'])
            overlap = (a == b or a in b.parents or b in a.parents or
                       (left['device'], left['inode']) == (right['device'], right['inode']))
            if overlap and not (same and left.get('aggregate_verified') is True
                                and right.get('aggregate_verified') is True):
                ambiguous.update((key, other))
    groups = {}
    for key, row in rows.items():
        if (row.get('verified') is True and row.get('aggregate_verified') is True
                and key not in ambiguous):
            identity = (row['scope'], row['device'], row['inode'])
            groups.setdefault(identity, []).append(key)
    grouped = {}
    for identity, members in groups.items():
        if len(members) < 2:
            continue
        first = members[0]
        amount = max(rows[key]['claim_bytes'] for key in members)
        live = max(rows[key]['live_bytes'] for key in members)
        grouped[first] = members
        rows[first].update(claim_bytes=amount, accounted_bytes=max(amount, live),
                           credited_bytes=min(amount, live), live_bytes=live,
                           members=members, reason='authenticated shared aggregate')
        for key in members[1:]:
            del rows[key]
    # Unauthenticated overlaps still cannot earn two credits.
    keys = [key for key in rows if rows[key].get('verified') is True]
    conflicts = set()
    for index, key in enumerate(keys):
        left = rows[key]
        for other in keys[index + 1:]:
            right = rows[other]
            a, b = Path(left['scope']), Path(right['scope'])
            if (a == b or a in b.parents or b in a.parents
                    or (left['device'], left['inode']) == (right['device'], right['inode'])):
                conflicts.update((key, other))
    for key in conflicts:
        rows[key].update(credited_bytes=0, reason='duplicate or overlapping scope')
    total = sum(row['claim_bytes'] for row in rows.values())
    accounted = sum(row['accounted_bytes'] for row in rows.values())
    credit = sum(row['credited_bytes'] for row in rows.values())
    unrealized = total - credit
    available_budget = available_bytes * 7 // 10
    cap = max(0, slice_max_bytes - headroom_bytes)
    room = max(0, min(available_budget - unrealized, cap - accounted))
    fits = unrealized + new_bytes <= available_budget and accounted + new_bytes <= cap
    return {'admitted': fits, 'fits': fits, 'MemAvailable_bytes': available_bytes,
            'budget_bytes': available_budget, 'slice_max_bytes': slice_max_bytes,
            'fixed_headroom_bytes': headroom_bytes, 'slice_claim_cap_bytes': cap,
            'active_claim_bytes': total, 'raw_claim_bytes': sum(claims.values()),
            'aggregate_groups': grouped, 'accounted_active_bytes': accounted,
            'live_over_booking_bytes': accounted-total, 'credited_live_bytes': credit,
            'unrealized_claim_bytes': unrealized, 'requested_total_bytes': accounted + new_bytes,
            'requested_unrealized_bytes': unrealized + new_bytes, 'new_claim_bytes': new_bytes,
            'available_new_claim_bytes': room, 'claim_observations': rows}


class ScopeReader:
    """Read owned receipts and kernel identities. Injection supports nonproof tests."""
    def __init__(self, *, proc=PROC, cgroup_root=CGROUP_ROOT, uid=None):
        self.proc = Path(proc)
        self.root = Path(cgroup_root)
        self.uid = os.getuid() if uid is None else uid
        self.parent = self.root / 'user.slice' / f'user-{self.uid}.slice' / f'user@{self.uid}.service' / 'zesuworkloads.slice'

    def directory(self, path):
        path = Path(path)
        if path != path.resolve(strict=True):
            raise ValueError('A cgroup path contains an alias.')
        info = path.stat()
        if not stat.S_ISDIR(info.st_mode):
            raise ValueError('The cgroup is not a directory.')
        return info.st_dev, info.st_ino

    def slice_max(self):
        try:
            before = self.directory(self.parent)
            maximum = int((self.parent / 'memory.max').read_text())
            swap = (self.parent / 'memory.swap.max').read_text().strip()
            if maximum != SLICE_MAX_BYTES or swap != '0' or self.directory(self.parent) != before:
                raise ValueError('The shared slice fence changed.')
            return maximum
        except (OSError, ValueError):
            return 0  # An unverifiable backstop cannot grant admission.

    def process(self, actor):
        pid, start = actor['pid'], actor['startticks']
        if type(pid) is not int or type(start) is not int or pid <= 0:
            raise ValueError('Invalid process identity.')
        path = self.proc / str(pid)
        fields = (path / 'stat').read_text().rsplit(')', 1)[1].split()
        if path.stat().st_uid != self.uid or fields[0] in ('Z', 'X', 'x') or int(fields[19]) != start:
            raise ValueError('The owned process identity changed.')
        return int(fields[1])

    def argv(self, actor):
        self.process(actor)
        return (self.proc / str(actor['pid']) / 'cmdline').read_bytes().decode().rstrip('\0').split('\0')

    @staticmethod
    def file_identity(info):
        return (info.st_dev, info.st_ino, info.st_size, info.st_mtime_ns,
                info.st_ctime_ns, info.st_mode, info.st_uid)

    def read(self, path):
        path = Path(path)
        info = path.lstat()
        if info.st_uid != self.uid or info.st_mode & 0o022 or not stat.S_ISREG(info.st_mode):
            raise ValueError('The ownership receipt is not private.')
        before = self.file_identity(info)
        with path.open('rb') as stream:
            if self.file_identity(os.fstat(stream.fileno())) != before:
                raise ValueError('The ownership receipt changed before reading.')
            raw = stream.read()
            if self.file_identity(os.fstat(stream.fileno())) != before:
                raise ValueError('The ownership receipt changed while reading.')
        if self.file_identity(path.lstat()) != before:
            raise ValueError('The ownership receipt changed after reading.')
        if hasattr(self, 'consulted'):
            self.consulted.append((path, before))
        return json.loads(raw)

    def ancestry(self, pid, ancestor):
        """Bind registry-wrapper children without using the owner's cgroup."""
        result=[]
        for _ in range(64):
            raw=(self.proc / str(pid) / 'stat').read_text().rsplit(')',1)[1].split()
            actor={'pid':pid,'startticks':int(raw[19])}
            parent=self.process(actor)
            result.append((actor,parent))
            if pid == ancestor['pid']:
                if actor['startticks'] != ancestor['startticks']:
                    raise ValueError('The batch ancestor identity changed.')
                return result
            if parent <= 1 or parent == pid:
                break
            pid=parent
        raise ValueError('The aggregate creator is outside the owned batch.')

    def scope(self, path, actor, batch, *, expected=None, leaf=False):
        self.process(batch)
        self.process(actor)
        path = Path(path)
        before = self.directory(path)
        if expected is not None and before != expected:
            raise ValueError('The aggregate inode changed.')
        aggregate = next((p for p in (path, *path.parents) if p.parent == self.parent), None)
        match = re.fullmatch(rf'zesuworkloads-aggregate{self.uid}p([0-9]+)r[0-9]+\.slice',
                             aggregate.name) if aggregate is not None else None
        if match is None:
            raise ValueError('The scope does not belong to a stock aggregate.')
        chain = self.ancestry(int(match[1]), batch)
        membership = (self.proc / str(actor['pid']) / 'cgroup').read_text().splitlines()
        relative = next(line[3:] for line in membership if line.startswith('0::'))
        actual = self.root / relative.lstrip('/')
        if (actual != path if leaf else actual != path and path not in actual.parents):
            raise ValueError('The recorded actor is outside its owned scope.')
        live = int((path / 'memory.current').read_text())
        integer(live, 'scope memory.current')
        self.process(actor)
        self.process(batch)
        if any(self.process(item) != parent for item,parent in chain):
            raise ValueError('The aggregate creator ancestry changed.')
        if self.directory(path) != before:
            raise ValueError('The scope changed during sampling.')
        if (self.proc / str(actor['pid']) / 'cgroup').read_text().splitlines() != membership:
            raise ValueError('The actor changed its scope during sampling.')
        return {'verified': True, 'aggregate_verified': path == aggregate,
                'scope': str(path), 'device': before[0], 'inode': before[1],
                'live_bytes': live, 'reason': 'exact owner and batch scope'}

    def output(self, data, key, owner, kind):
        location = data.get('claim_locations', {}).get(key)
        if location is not None:
            if location['owner'] != owner or location['kind'] != kind:
                raise ValueError('The claim location owner changed.')
            return Path(location['output_path'])
        argv = self.argv(owner)
        if kind == 'entry':
            # Retained controllers bind the exact output as their final argument.
            for index, argument in enumerate(argv):
                if Path(argument).name == 'entry_chain_run.py' and len(argv[index + 1:]) == 4:
                    if argv[-2] != owner['block'] or key != 'EntryChain_' + owner['block'] + '_' + owner['token']:
                        raise ValueError('The retained controller token changed.')
                    return Path(argv[-1])
            raise ValueError('The retained entry controller lacks an output binding.')
        if kind == 'gate':
            cwd = (self.proc / str(owner['pid']) / 'cwd').resolve(strict=True)
            run = owner['run_id']
            if Path(run).name != run:
                raise ValueError('The gate run identity is invalid.')
            return cwd / '_build/agents/correctness-gates' / run
        raise ValueError('The legacy claim lacks a verifiable scope.')

    def claim(self, data, key):
        self.consulted = []
        try:
            if key in data.get('shell_claim_owners', {}):
                record = data['shell_claim_owners'][key]
                marker = Path(record['marker'])
                before = self.file_identity(marker.lstat())
                if tuple(record.get('token_identity', ())) != before:
                    raise ValueError('The admitted shell token identity changed.')
                fields = dict(line.split('=', 1) for line in marker.read_text().splitlines()[1:] if '=' in line)
                if fields.get('reservation_generation') != record['generation']:
                    raise ValueError('The admitted shell generation changed.')
                sample = self.shell(marker, owner=record['owner'])
                if self.file_identity(marker.lstat()) != before:
                    raise ValueError('The admitted shell token changed during sampling.')
                return sample
            if key in data.get('entry_pilot_outside_owners', {}):
                kind, owner = 'entry', data['entry_pilot_outside_owners'][key]
            elif key in data.get('correctness_gate_owners', {}):
                kind, owner = 'gate', data['correctness_gate_owners'][key]
            else:
                raise ValueError('The claim lacks an owned batch binding.')
            self.process(owner)
            out = self.output(data, key, owner, kind)
            batch = self.read(out / 'BATCH-PROCESS.json')
            if self.process(batch) != owner['pid']:
                raise ValueError('The batch process has another owner.')
            if kind == 'entry':
                if self.read(out / 'STARTED.json')['owner'] != owner:
                    raise ValueError('The entry token differs from its ledger owner.')
                if key != 'EntryChain_' + owner['block'] + '_' + owner['token']:
                    raise ValueError('The entry claim token changed.')
                bound = self.read(out / 'BATCH-IDENTITY.json')
                actor = {'pid': bound['inside_pid'], 'startticks': bound['inside_startticks']}
                args = self.argv(actor)
                if args[-2:] != ['--inside', str(out)] or Path(args[-3]).name != 'entry_chain_run.py':
                    raise ValueError('The inside controller belongs to another output.')
                row = self.scope(bound['aggregate_path'], actor, batch,
                                 expected=(bound['aggregate_device'], bound['aggregate_inode']))
            else:
                request = self.read(out / 'REQUEST.json')
                if request['owner'] != owner or request['policy']['claim_key'] != key:
                    raise ValueError('The gate request owner changed.')
                bound = self.read(out / 'BATCH.json')
                if len(bound['actors']) != 1 or len(bound['aggregate_paths']) != 1:
                    raise ValueError('The gate batch scope is ambiguous.')
                actor = bound['actors'][0]
                args = self.argv(actor)
                if args[-2:] != ['inside', str(out)] or Path(args[-3]).name != 'correctness_gate.py':
                    raise ValueError('The gate actor belongs to another output.')
                row = self.scope(bound['aggregate_paths'][0], actor, batch)
            self.process(owner)
            if any(self.file_identity(path.lstat()) != identity for path,identity in self.consulted):
                raise ValueError('The claim ownership receipts changed during sampling.')
            return row
        except (OSError, ValueError, KeyError, IndexError, StopIteration, TypeError) as error:
            return {'verified': False, 'live_bytes': 0, 'reason': str(error)}

    def residual(self, bound):
        """Sample a previously authenticated aggregate after its token ends."""
        try:
            path = Path(bound['scope'])
            if path.resolve() != path:
                raise ValueError('The retained aggregate contains an alias.')
            if path.parent != self.parent or not re.fullmatch(
                    rf'zesuworkloads-aggregate{self.uid}p[0-9]+r[0-9]+\.slice', path.name):
                raise ValueError('The retained aggregate namespace changed.')
            if not path.exists():
                if path.is_symlink():
                    raise ValueError('The retained aggregate is an alias.')
                return {'verified': True, 'closed': True, 'live_bytes': 0}
            before = self.directory(path)
            if before != (bound['device'], bound['inode']):
                raise ValueError('The retained aggregate identity changed.')
            live = int((path / 'memory.current').read_text())
            events = (path / 'cgroup.events').read_text()
            if self.directory(path) != before:
                raise ValueError('The retained aggregate changed during sampling.')
            integer(live, 'retained aggregate memory')
            if 'populated 0' in events.splitlines():
                return {'verified': True, 'closed': True, 'live_bytes': 0}
            if 'populated 1' not in events.splitlines():
                raise ValueError('The retained aggregate population is unknown.')
            return dict(bound, verified=True, aggregate_verified=True, live_bytes=live,
                        reason='authenticated aggregate remains populated')
        except (OSError, ValueError, KeyError, TypeError) as error:
            return {'verified': False, 'live_bytes': 0, 'reason': str(error)}

    def shell(self, marker, *, owner=None):
        """Authenticate an admitted or pending shell owner's actual aggregate."""
        try:
            path = Path(marker)
            before = self.file_identity(path.lstat())
            info = path.lstat()
            if info.st_uid != self.uid or info.st_mode & 0o022 or not stat.S_ISREG(info.st_mode):
                raise ValueError('The shell token is not private.')
            lines = path.read_text().splitlines()
            fields = dict(line.split('=', 1) for line in lines[1:] if '=' in line)
            if len(fields) != len([line for line in lines[1:] if '=' in line]):
                raise ValueError('The shell token repeats a field.')
            expected = {'pid': int(path.name.split('.')[0]), 'startticks': int(fields['owner_start'])} if owner is None else owner
            if int(fields['owner_start']) != expected['startticks']:
                raise ValueError('The shell token owner changed.')
            self.process(expected)
            if lines[0].isdecimal():
                leaf = self.compiler(path)
                if leaf.get('verified') is not True:
                    raise ValueError('The marked shell child is not authenticated.')
                leaf_path = Path(leaf['scope'])
                if leaf_path.parent == self.parent:
                    return leaf
                aggregate = next(p for p in leaf_path.parents if p.parent == self.parent)
                creator = int(re.fullmatch(rf'zesuworkloads-aggregate{self.uid}p([0-9]+)r[0-9]+\.slice', aggregate.name)[1])
                raw = (self.proc / str(creator) / 'stat').read_text().rsplit(')', 1)[1].split()
                batch = {'pid': creator, 'startticks': int(raw[19])}
                actor = {'pid': int(lines[0]), 'startticks': int(fields['child_start'])}
                row = self.scope(aggregate, actor, batch)
                if self.file_identity(path.lstat()) != before:
                    raise ValueError('The marked token changed during aggregate sampling.')
                return row
            membership = (self.proc / str(expected['pid']) / 'cgroup').read_text()
            relative = next(line[3:] for line in membership.splitlines() if line.startswith('0::'))
            actual = self.root / relative.lstrip('/')
            aggregate = next(p for p in (actual, *actual.parents) if p.parent == self.parent)
            if aggregate.name != fields.get('aggregate'):
                raise ValueError('The pending owner is outside its declared aggregate.')
            match = re.fullmatch(rf'zesuworkloads-aggregate{self.uid}p([0-9]+)r[0-9]+\.slice', aggregate.name)
            if match is None:
                raise ValueError('The shell aggregate name is invalid.')
            creator = int(match[1])
            raw = (self.proc / str(creator) / 'stat').read_text().rsplit(')', 1)[1].split()
            batch = {'pid': creator, 'startticks': int(raw[19])}
            chain = self.ancestry(expected['pid'], batch)
            row = self.scope(aggregate, expected, batch)
            if (self.file_identity(path.lstat()) != before
                    or (self.proc / str(expected['pid']) / 'cgroup').read_text() != membership
                    or any(self.process(actor) != parent for actor, parent in chain)):
                raise ValueError('The shell ownership changed during sampling.')
            return row
        except (OSError, ValueError, KeyError, IndexError, StopIteration, TypeError) as error:
            return {'verified': False, 'live_bytes': 0, 'reason': str(error)}

    def compiler(self, marker):
        """A compiler gets only its unique leaf scope, never its shared aggregate."""
        try:
            marker = Path(marker)
            marker_before = self.file_identity(marker.lstat())
            if marker.lstat().st_uid != self.uid or not stat.S_ISREG(marker.lstat().st_mode) or marker.lstat().st_mode & 0o022:
                raise ValueError('The compiler reservation is not private.')
            lines = marker.read_text().splitlines()
            pairs = [line.split('=', 1) for line in lines[1:] if '=' in line]
            fields = dict(pairs)
            if len(fields) != len(pairs):
                raise ValueError('The compiler reservation repeats a field.')
            owner = {'pid': int(marker.name.split('.')[0]), 'startticks': int(fields['owner_start'])}
            actor = {'pid': int(lines[0]), 'startticks': int(fields['child_start'])}
            self.process(actor)
            self.process(owner)
            environment = dict(item.split('=', 1) for item in
                (self.proc / str(actor['pid']) / 'environ').read_bytes().decode().split('\0')
                if '=' in item)
            if any(environment.get(name) != str(marker) for name in
                   ('ZESU_COQC_SCOPE', 'ZESU_COQC_RESERVATION')):
                raise ValueError('The compiler does not carry this exact reservation token.')
            relative = next(line[3:] for line in (self.proc / str(actor['pid']) / 'cgroup').read_text().splitlines() if line.startswith('0::'))
            path = self.root / relative.lstrip('/')
            if not re.fullmatch(rf'zesudet-.+-{owner["pid"]}-[0-9]+\.scope', path.name):
                raise ValueError('The compiler lacks its own guarded leaf scope.')
            if path.parent == self.parent:
                writer = fields.get('writer', '')
                if (not re.fullmatch(r'[a-zA-Z0-9._-]+', writer)
                        or environment.get('ZESU_WRITER_ID') != writer
                        or not path.name.startswith('zesudet-writer-' + writer + '-')):
                    raise ValueError('The standalone compiler lacks its writer identity.')
                chain = self.ancestry(actor['pid'], owner)
                before = self.directory(path)
                live = int((path / 'memory.current').read_text())
                integer(live, 'standalone compiler memory')
                if (self.directory(path) != before or self.file_identity(marker.lstat()) != marker_before
                        or any(self.process(item) != parent for item, parent in chain)
                        or next(line[3:] for line in (self.proc / str(actor['pid']) / 'cgroup').read_text().splitlines()
                                if line.startswith('0::')) != relative):
                    raise ValueError('The standalone compiler identity changed.')
                return {'verified': True, 'aggregate_verified': False, 'scope': str(path),
                        'device': before[0], 'inode': before[1], 'live_bytes': live,
                        'reason': 'exact standalone writer leaf'}
            aggregate = next(p for p in path.parents if p.parent == self.parent)
            if aggregate.name != fields['aggregate']:
                raise ValueError('The compiler aggregate differs from its reservation.')
            pid = int(re.fullmatch(r'zesuworkloads-aggregate[0-9]+p([0-9]+)r[0-9]+\.slice', aggregate.name)[1])
            # The live batch PID is the guard that created this unique aggregate.
            raw = (self.proc / str(pid) / 'stat').read_text().rsplit(')', 1)[1].split()
            batch = {'pid': pid, 'startticks': int(raw[19])}
            try:
                owner_chain = self.ancestry(owner['pid'], batch)
            except ValueError:
                owner_chain = self.ancestry(batch['pid'], owner)
            row = self.scope(path, actor, batch, leaf=True)
            if any(self.process(item) != parent for item,parent in owner_chain):
                raise ValueError('The compiler owner ancestry changed.')
            self.process(owner)
            if self.file_identity(marker.lstat()) != marker_before:
                raise ValueError('The compiler reservation changed during sampling.')
            return row
        except (OSError, ValueError, KeyError, IndexError, StopIteration, TypeError) as error:
            return {'verified': False, 'live_bytes': 0, 'reason': str(error)}


DEFAULT_LEDGER = Path('/home/cody/zesislar/_build/agents/worker-build-2/native-region-release-v1/LEDGER.json')


def marker_directory():
    return Path(os.environ.get('ZESU_GUARD_STATE',
                str(Path(os.environ.get('XDG_RUNTIME_DIR', '/tmp')) / 'zesu-guard'))) / 'coqc-reservations'


def shell_key(marker):
    return 'shell:' + hashlib.sha256(str(Path(marker).absolute()).encode()).hexdigest()


def shell_rows(data, reader):
    """Read legacy tokens without migration, deletion, or a second ledger."""
    directory = Path(data.get('shell_marker_directory', marker_directory()))
    if directory.is_symlink() or directory.resolve() != directory:
        raise ValueError('The shell reservation directory contains an alias.')
    rows = {}
    for marker in sorted(directory.glob('*')):
        try:
            info = marker.lstat()
            if not stat.S_ISREG(info.st_mode) or info.st_uid != reader.uid or info.st_mode & 0o022:
                raise ValueError('A shell reservation is not private.')
            before = reader.file_identity(info)
            lines = marker.read_text().splitlines()
            if not lines or lines[0] == 'pending':
                continue
            fields = dict(line.split('=', 1) for line in lines[1:] if '=' in line)
            if len(fields) != len([line for line in lines[1:] if '=' in line]):
                raise ValueError('A shell reservation repeats a field.')
            fence = int(fields.get('memory_fence_bytes', int(fields.get('memory_gib', 64)) * GIB))
            amount = max(int(fields.get('memory_claim_bytes', fence)),
                         int(fields.get('memory_probe_claim_bytes', 0)))
            if shell_key(marker) not in data.get('shell_claim_owners', {}):
                amount = max(amount, fence)
            integer(amount, 'shell booking')
            if reader.file_identity(marker.lstat()) != before:
                raise ValueError('A shell reservation changed while reading.')
            observation = reader.shell(marker)
            if (shell_key(marker) not in data.get('shell_claim_owners', {})
                    and observation.get('aggregate_verified') is True):
                try:
                    amount = max(amount, aggregate_fence(reader, observation))
                except (OSError, ValueError):
                    observation = {'verified': False, 'live_bytes': 0, 'reason': 'legacy aggregate fence is unknown'}
            rows[shell_key(marker)] = (amount, observation)
        except FileNotFoundError:
            raise ValueError('A shell token disappeared during the shared projection.')
    return rows


def projection(data, claims, new_bytes, available_bytes, *, reader=None, new_observation=None):
    reader = ScopeReader() if reader is None else reader
    claims = dict(claims)
    observations = {key: reader.claim(data, key) for key, amount in claims.items() if amount}
    # Legacy writers stay visible until rollout closes or updates them.
    # Non-kernel unit readers supply their own inventory explicitly.
    if isinstance(reader, ScopeReader) and (reader.proc == PROC or 'shell_marker_directory' in data):
        for key, (amount, observation) in shell_rows(data, reader).items():
            claims[key] = max(claims.get(key, 0), amount)
            if key not in data.get('shell_claim_owners', {}):
                observations[key] = observation
    retained_groups = dict(data.get('legacy_aggregate_holds', {}))
    retained_groups.update(data.get('shell_aggregate_holds', {}))
    for key, retained in retained_groups.items():
        sample = reader.residual(retained['aggregate'])
        if sample.get('closed') is True:
            continue
        # An unknown retained scope keeps its last booking. A verified live
        # aggregate contributes actual usage even after its final token ends.
        claims[key] = retained['fallback_bytes']
        observations[key] = sample
    return dict(evaluate(claims, new_bytes, available_bytes, observations=observations,
                         new_observation=new_observation,
                         slice_max_bytes=reader.slice_max()), admission_pool='canonical', memory_ledger='unified')


def aggregate_fence(reader, observation):
    path = Path(observation['scope'])
    before = reader.directory(path)
    if before != (observation['device'], observation['inode']):
        raise ValueError('The legacy aggregate identity changed.')
    fence = int((path / 'memory.max').read_text())
    if fence <= 0 or fence > SLICE_MAX_BYTES or (path / 'memory.swap.max').read_text().strip() != '0':
        raise ValueError('The legacy aggregate fence is not authorized.')
    if reader.directory(path) != before or int((path / 'memory.max').read_text()) != fence:
        raise ValueError('The legacy aggregate fence changed during sampling.')
    return fence


def prepare_legacy_rollout(data, writers, *, reader=None):
    """Build a reviewed seed in memory. Never migrate or delete a live claim.

    The coordinator must supply and review the complete old-writer inventory.
    Only one-shot stock guards already bound to represented aggregates qualify.
    An arbitrary old controller or future aggregate creator blocks the switch.
    """
    reader = ScopeReader() if reader is None else reader
    holds = {}
    for writer in writers:
        owner = writer['owner']
        reader.process(owner)
        source = writer['source']
        if hashlib.sha256(Path(source['path']).read_bytes()).hexdigest() != source['sha256']:
            raise ValueError('The legacy writer source changed.')
        argv = reader.argv(owner)
        if argv != writer['argv']:
            raise ValueError('The legacy writer command changed.')
        command_end = argv.index('--') if '--' in argv else len(argv)
        positions = [i for i, word in enumerate(argv[:command_end])
                     if Path(word).name == 'resource_guard.sh']
        if len(positions) != 1 or Path(argv[positions[0]]).resolve() != Path(source['path']).resolve():
            raise ValueError('An old writer can create an unrepresented aggregate.')
        mode = argv[positions[0] + 1] if positions[0] + 1 < len(argv) else None
        if mode not in ('scope', 'scope-exec', 'batch'):
            raise ValueError('An old writer can create an unrepresented aggregate.')
        observation = reader.shell(writer['marker'], owner=owner)
        if observation.get('aggregate_verified') is not True:
            raise ValueError('The old writer has no authenticated aggregate.')
        path = Path(observation['scope'])
        if mode == 'batch':
            if re.fullmatch(rf'zesuworkloads-aggregate{reader.uid}p{owner["pid"]}r[0-9]+\.slice', path.name) is None:
                raise ValueError('The old batch has not created its exact aggregate.')
        else:
            environment = dict(item.split('=', 1) for item in
                (reader.proc / str(owner['pid']) / 'environ').read_bytes().decode().split('\0') if '=' in item)
            if environment.get('ZESU_AGGREGATE_SLICE') != path.name:
                raise ValueError('The old scope can create an unrepresented aggregate.')
        fence = aggregate_fence(reader, observation)
        identity = f"{path}:{observation['device']}:{observation['inode']}"
        key = 'legacy-aggregate:' + hashlib.sha256(identity.encode()).hexdigest()
        holds[key] = {'aggregate': {name: observation[name] for name in ('scope', 'device', 'inode')},
                      'fallback_bytes': fence, 'writer': owner, 'source': source}
        reader.process(owner)
    result = dict(data)
    result['legacy_aggregate_holds'] = dict(data.get('legacy_aggregate_holds', {}), **holds)
    return result


@contextmanager
def guard_lock():
    """Take GATE_MUTEX before LEDGER.lock. Shell children reuse its exact FD."""
    path = Path(os.environ.get('ZESU_GATE_LOCK', '/tmp/zesu-gate.lock') + '.mutex')
    if path.resolve() != path or path.is_symlink():
        raise ValueError('The guard mutex path contains an alias.')
    inherited = os.environ.get('ZESU_GUARD_MUTEX_FD')
    if inherited is not None:
        if not inherited.isdecimal():
            raise ValueError('The inherited guard descriptor is invalid.')
        descriptor = int(inherited)
        info, expected = os.fstat(descriptor), path.lstat()
        if ((info.st_dev, info.st_ino) != (expected.st_dev, expected.st_ino)
                or info.st_uid != os.getuid() or info.st_mode & 0o022
                or not stat.S_ISREG(info.st_mode)):
            raise ValueError('The inherited descriptor names another guard mutex.')
        try:
            fcntl.flock(descriptor, fcntl.LOCK_EX | fcntl.LOCK_NB)
        except BlockingIOError:
            raise ValueError('The inherited guard mutex is held by another owner.')
        current = path.lstat()
        if (current.st_dev, current.st_ino) != (info.st_dev, info.st_ino):
            raise ValueError('The inherited guard mutex changed.')
        # Never unlock the shared open description. The shell owns its lifetime.
        yield
        return
    descriptor = os.open(path, os.O_WRONLY | os.O_APPEND | os.O_CREAT | os.O_NOFOLLOW, 0o600)
    try:
        info = os.fstat(descriptor)
        if info.st_uid != os.getuid() or info.st_mode & 0o022 or not stat.S_ISREG(info.st_mode):
            raise ValueError('The guard mutex is not owned.')
        fcntl.flock(descriptor, fcntl.LOCK_EX)
        current = path.lstat()
        if (current.st_dev, current.st_ino) != (info.st_dev, info.st_ino):
            raise ValueError('The guard mutex changed while waiting.')
        yield
    finally:
        os.close(descriptor)


@contextmanager
def ledger_transaction(ledger):
    ledger = Path(ledger)
    if ledger.is_symlink() or ledger.name != 'LEDGER.json':
        raise ValueError('The unified ledger path is invalid.')
    lock = ledger.with_name('LEDGER.lock')
    if lock.is_symlink():
        raise ValueError('The unified ledger lock is an alias.')
    with guard_lock(), lock.open('a') as stream:
        fcntl.flock(stream, fcntl.LOCK_EX)
        info = ledger.lstat()
        if info.st_uid != os.getuid() or info.st_mode & 0o022 or not stat.S_ISREG(info.st_mode):
            raise ValueError('The unified ledger is not owned.')
        yield json.loads(ledger.read_text())


def write_ledger(path, data):
    path = Path(path)
    fd, name = tempfile.mkstemp(prefix='.LEDGER.', dir=path.parent)
    try:
        with os.fdopen(fd, 'w') as stream:
            json.dump(data, stream, indent=2)
            stream.write('\n'); stream.flush(); os.fsync(stream.fileno())
        os.replace(name, path)
    finally:
        Path(name).unlink(missing_ok=True)


def ledger_claims(data):
    claims = dict(data['fixed_claims'])
    for name, amount in data.get('region_claims', {}).items():
        release = data.get('released_region_claims', {}).get(name)
        if (release and release.get('bytes') == amount
                and hashlib.sha256(Path(release['receipt']).read_bytes()).hexdigest() == release['sha256']):
            continue
        claims['legacy:' + name] = amount
    return claims


def current_projection(request_bytes, available_bytes, *, ledger=None, reader=None):
    ledger = Path(ledger or os.environ.get('ZESU_CANONICAL_LEDGER', DEFAULT_LEDGER))
    with ledger_transaction(ledger) as data:
        return projection(data, ledger_claims(data), request_bytes, available_bytes, reader=reader)


def confirm_shell(marker, replacement, request_bytes, available_bytes, *, ledger=None, reader=None):
    """Publish one shell token and its claim under the canonical transaction lock.

    Both routes take GATE_MUTEX before LEDGER.lock. Shell helpers reuse its FD.
    A publication failure retains the ledger claim conservatively.
    """
    marker, replacement = Path(marker).absolute(), Path(replacement).absolute()
    ledger = Path(ledger or os.environ.get('ZESU_CANONICAL_LEDGER', DEFAULT_LEDGER))
    reader = ScopeReader() if reader is None else reader
    integer(request_bytes, 'shell request')
    replacement_identity = reader.file_identity(replacement.lstat())
    fields = dict(line.split('=', 1) for line in replacement.read_text().splitlines()[1:] if '=' in line)
    amount = max(int(fields['memory_claim_bytes']), int(fields.get('memory_probe_claim_bytes', 0)))
    if amount != request_bytes:
        raise ValueError('The shell request differs from its effective token booking.')
    generation = fields['reservation_generation']
    if not re.fullmatch(r'[a-zA-Z0-9-]{16,80}', generation):
        raise ValueError('The reservation generation is invalid.')
    owner = {'pid': int(marker.name.split('.')[0]), 'startticks': int(fields['owner_start'])}
    reader.process(owner)
    key = shell_key(marker)
    with ledger_transaction(ledger) as data:
        if marker.exists() or marker.is_symlink() or key in data.get('shell_claim_owners', {}):
            raise ValueError('The shell token already exists.')
        if marker.name.partition('.')[2] != generation:
            raise ValueError('The token path differs from its immutable generation.')
        expected_directory = Path(data.get('shell_marker_directory', marker_directory()))
        if (marker.parent != expected_directory or marker.parent.resolve() != marker.parent
                or not re.fullmatch(r'[0-9]+\.[a-zA-Z0-9.-]+', marker.name)):
            raise ValueError('The shell token is outside its owned namespace.')
        observation = reader.shell(replacement, owner=owner)
        claims = ledger_claims(data)
        result = projection(data, claims, request_bytes, available_bytes,
                            reader=reader, new_observation=observation)
        if not result['fits']:
            return result
        reader.process(owner)
        if reader.file_identity(replacement.lstat()) != replacement_identity:
            raise ValueError('The pending shell token changed.')
        # Publish the booking first. An interrupted token publication cannot underbook.
        data['fixed_claims'][key] = request_bytes
        data.setdefault('shell_claim_owners', {})[key] = {'owner': owner, 'marker': str(marker),
            'aggregate': observation if observation.get('aggregate_verified') is True else None,
            'generation': generation}
        data.setdefault('shell_admissions', {})[key] = result
        write_ledger(ledger, data)
        os.replace(replacement, marker)
        data['shell_claim_owners'][key]['token_identity'] = reader.file_identity(marker.lstat())
        write_ledger(ledger, data)
        return result


def read_shell_bookings(*, ledger=None):
    ledger = Path(ledger or os.environ.get('ZESU_CANONICAL_LEDGER', DEFAULT_LEDGER))
    with ledger_transaction(ledger) as data:
        return {row['marker']: data['fixed_claims'].get(key, 0)
                for key, row in data.get('shell_claim_owners', {}).items()}


def refresh_shell_growth(growth, *, ledger=None, reader=None):
    """Commit monotonic observations without replacing reservation tokens."""
    if not growth:
        return
    reader = ScopeReader() if reader is None else reader
    ledger = Path(ledger or os.environ.get('ZESU_CANONICAL_LEDGER', DEFAULT_LEDGER))
    with ledger_transaction(ledger) as data:
        for row in growth:
            marker = Path(row['reservation']).absolute()
            amount = integer(row['claim_bytes'], 'observed shell growth')
            key = shell_key(marker)
            record = data.get('shell_claim_owners', {}).get(key)
            if record is not None:
                if data['fixed_claims'].get(key, 0) <= 0:
                    raise ValueError('Growth cannot revive a released shell token.')
                sample = reader.claim(data, key)
                if sample.get('verified') is not True:
                    raise ValueError('Growth lacks an authenticated shell token.')
                data['fixed_claims'][key] = max(data['fixed_claims'][key], amount)
            else:
                sample = reader.shell(marker)
                matching = [hold for hold in data.get('legacy_aggregate_holds', {}).values()
                            if all(hold['aggregate'].get(name) == sample.get(name)
                                   for name in ('scope', 'device', 'inode'))]
                if sample.get('aggregate_verified') is not True or len(matching) != 1:
                    raise ValueError('Legacy growth lacks its authenticated aggregate hold.')
                matching[0]['fallback_bytes'] = max(matching[0]['fallback_bytes'], amount)
            data.setdefault('shell_growth', []).append(dict(row, claim_key=key))
        write_ledger(ledger, data)


def mark_shell(marker, *, ledger=None, reader=None):
    """Bind the actual guarded compiler leaf after systemd starts it."""
    marker = Path(marker).absolute()
    reader = ScopeReader() if reader is None else reader
    ledger = Path(ledger or os.environ.get('ZESU_CANONICAL_LEDGER', DEFAULT_LEDGER))
    with ledger_transaction(ledger) as data:
        record = data.get('shell_claim_owners', {}).get(shell_key(marker))
        if record is None:
            return False
        if data['fixed_claims'].get(shell_key(marker), 0) <= 0:
            raise ValueError('The marked shell booking is already released.')
        lines = marker.read_text().splitlines()
        fields = dict(line.split('=', 1) for line in lines[1:] if '=' in line)
        if (fields.get('reservation_generation') != record['generation']
                or int(fields['owner_start']) != record['owner']['startticks']):
            raise ValueError('The marked reservation generation changed.')
        sample = reader.compiler(marker)
        if sample.get('verified') is not True:
            raise ValueError('The marked compiler lacks an authenticated leaf.')
        record['leaf'] = {name: sample[name] for name in ('scope', 'device', 'inode')}
        record['token_identity'] = reader.file_identity(marker.lstat())
        write_ledger(ledger, data)
        return True


def leaf_closed(reader, bound):
    path = Path(bound['scope'])
    if path.resolve() != path:
        raise ValueError('The released leaf contains an alias.')
    if not path.exists():
        if path.is_symlink():
            raise ValueError('The released leaf is an alias.')
        return True
    before = reader.directory(path)
    if before != (bound['device'], bound['inode']):
        raise ValueError('The released leaf identity changed.')
    events = (path / 'cgroup.events').read_text().splitlines()
    if reader.directory(path) != before:
        raise ValueError('The released leaf changed during sampling.')
    return 'populated 0' in events


def release_shell(marker, *, ledger=None, reader=None):
    """Release only an exact token whose recorded compiler actor ended."""
    marker = Path(marker).absolute()
    ledger = Path(ledger or os.environ.get('ZESU_CANONICAL_LEDGER', DEFAULT_LEDGER))
    reader = ScopeReader() if reader is None else reader
    with ledger_transaction(ledger) as data:
        key = shell_key(marker)
        record = data.get('shell_claim_owners', {}).get(key)
        if record is None:
            token_identity = reader.file_identity(marker.lstat())
            raw = marker.read_bytes()
            fields = dict(line.split('=', 1) for line in raw.decode().splitlines()[1:] if '=' in line)
            matching = [hold for hold in data.get('legacy_aggregate_holds', {}).values()
                        if Path(hold['aggregate']['scope']).name == fields.get('aggregate')]
            if len(matching) != 1 or reader.residual(matching[0]['aggregate']).get('closed') is not True:
                raise ValueError('The legacy token lacks authenticated aggregate closure.')
            if reader.file_identity(marker.lstat()) != token_identity:
                raise ValueError('The legacy token changed during reclamation.')
            data.setdefault('legacy_shell_releases', {})[key] = {
                'marker': str(marker), 'token_sha256': hashlib.sha256(raw).hexdigest(),
                'aggregate': matching[0]['aggregate']}
            write_ledger(ledger, data)
            marker.unlink()
            return True
        token_identity = reader.file_identity(marker.lstat())
        if tuple(record.get('token_identity', ())) != token_identity:
            raise ValueError('The released token identity changed.')
        lines = marker.read_text().splitlines()
        fields = dict(line.split('=', 1) for line in lines[1:] if '=' in line)
        if (fields.get('reservation_generation') != record['generation']
                or int(fields['owner_start']) != record['owner']['startticks']):
            raise ValueError('The release owner differs from its token.')
        if lines[0].isdecimal():
            if not record.get('leaf') or not leaf_closed(reader, record['leaf']):
                raise ValueError('The exact shell compiler leaf is not closed.')
            actor = {'pid': int(lines[0]), 'startticks': int(fields['child_start'])}
            try:
                path = reader.proc / str(actor['pid'])
                raw = (path / 'stat').read_text().rsplit(')', 1)[1].split()
                if path.stat().st_uid != reader.uid:
                    raise ValueError('The shell compiler UID changed.')
                if int(raw[19]) == actor['startticks'] and raw[0] not in ('Z', 'X', 'x'):
                    raise ValueError('The shell compiler actor is not closed.')
            except FileNotFoundError:
                pass
        if lines[0] == 'confirmed':
            reader.process(record['owner'])
        sample = reader.residual(record['aggregate']) if record.get('aggregate') else {}
        if sample.get('closed') is True:
            sample = dict(record['aggregate'], aggregate_verified=True)
        if sample.get('aggregate_verified') is True:
            aggregate_identity = str(sample['scope']) + ':' + str(sample['device']) + ':' + str(sample['inode'])
            hold = 'shell-aggregate:' + hashlib.sha256(aggregate_identity.encode()).hexdigest()
            data.setdefault('shell_aggregate_holds', {})[hold] = {
                'aggregate': {name: sample[name] for name in ('scope', 'device', 'inode')},
                'fallback_bytes': max(data['fixed_claims'][key],
                    data.get('shell_aggregate_holds', {}).get(hold, {}).get('fallback_bytes', 0))}
        elif record.get('aggregate') or not (lines[0].isdecimal() and record.get('leaf') and leaf_closed(reader, record['leaf'])):
            raise ValueError('The shell aggregate closure cannot be authenticated.')
        if reader.file_identity(marker.lstat()) != token_identity:
            raise ValueError('The released token changed during validation.')
        data['fixed_claims'][key] = 0
        data.setdefault('shell_releases', {})[key] = {'marker': str(marker), 'owner': record['owner']}
        write_ledger(ledger, data)
        marker.unlink()
        return True
