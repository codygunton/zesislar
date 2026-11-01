"""Account reservations and verified live usage against both memory limits.

Only an exact owner token, batch identity, and live kernel membership can earn
memory.current credit. Missing evidence retains the complete reservation.
"""
import json
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


def evaluate(claims, new_bytes, available_bytes, *, observations=None,
             slice_max_bytes=None, headroom_bytes=HEADROOM_BYTES):
    """Evaluate both inequalities. Observations come from ScopeReader only."""
    for key, amount in claims.items():
        integer(amount, key)
    integer(new_bytes, 'new claim')
    integer(available_bytes, 'available memory')
    integer(headroom_bytes, 'fixed headroom')
    if slice_max_bytes is None:
        slice_max_bytes = ScopeReader().slice_max()
    integer(slice_max_bytes, 'verified slice maximum')
    rows = {}
    observations = observations or {}
    for key, amount in claims.items():
        if not amount:
            continue
        row = observations.get(key, {})
        live = row.get('live_bytes', 0) if row.get('verified') is True else 0
        integer(live, 'verified live memory')
        rows[key] = dict(row, claim_bytes=amount, accounted_bytes=max(amount, live),
                         credited_bytes=min(amount, live),
                         reason=row.get('reason', 'unverified scope'))
    # Parent/child aggregates and duplicate scope identities cannot earn two credits.
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
    total = sum(claims.values())
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
            'active_claim_bytes': total, 'accounted_active_bytes': accounted,
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
        return {'verified': True, 'scope': str(path), 'device': before[0], 'inode': before[1],
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
            aggregate = next(p for p in path.parents if p.parent == self.parent)
            if aggregate.name != fields['aggregate']:
                raise ValueError('The compiler aggregate differs from its reservation.')
            pid = int(re.fullmatch(r'zesuworkloads-aggregate[0-9]+p([0-9]+)r[0-9]+\.slice', aggregate.name)[1])
            # The live batch PID is the guard that created this unique aggregate.
            raw = (self.proc / str(pid) / 'stat').read_text().rsplit(')', 1)[1].split()
            batch = {'pid': pid, 'startticks': int(raw[19])}
            owner_chain = self.ancestry(owner['pid'], batch)
            row = self.scope(path, actor, batch, leaf=True)
            if any(self.process(item) != parent for item,parent in owner_chain):
                raise ValueError('The compiler owner ancestry changed.')
            self.process(owner)
            if self.file_identity(marker.lstat()) != marker_before:
                raise ValueError('The compiler reservation changed during sampling.')
            return row
        except (OSError, ValueError, KeyError, IndexError, StopIteration, TypeError) as error:
            return {'verified': False, 'live_bytes': 0, 'reason': str(error)}


def projection(data, claims, new_bytes, available_bytes, *, reader=None):
    reader = ScopeReader() if reader is None else reader
    observations = {key: reader.claim(data, key) for key, amount in claims.items() if amount}
    return dict(evaluate(claims, new_bytes, available_bytes, observations=observations,
                         slice_max_bytes=reader.slice_max()), admission_pool='canonical')
