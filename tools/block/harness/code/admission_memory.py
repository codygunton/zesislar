"""Account reservations and verified live usage against both memory limits.

Only an exact owner token, batch identity, and live kernel membership can earn
memory.current credit. Missing evidence retains the complete reservation.
"""
import json
import fcntl
import hashlib
import tempfile
from contextlib import contextmanager
from contextvars import ContextVar
import os
from pathlib import Path
import re
import stat
import sys
import time

GIB = 1024 ** 3
HEADROOM_BYTES = 20 * GIB
SLICE_MAX_BYTES = 175 * GIB
STATIC_KERNEL_ACCOUNT_SCHEMA = 'legacy_kernel_accounts.v1'
CGROUP_ROOT = Path('/sys/fs/cgroup')
PROC = Path('/proc')
# Preserve only these byte-exact public templates from the accepted predecessor.
PUBLIC_GUARD_HISTORY = {
    'commit': '76a6622449395debea3b224bd6c5b981e61fd7d0',
    'templates': {
        'tools/resource_guard.sh': 'fd70d33ffc7a8515141529f4f1ba43df56e265d4c2df5c27fa7cb2ee7a4666f1',
        'tools/block/harness/runtime-tools/resource_guard.sh': '6e4940725cf327cc7bc1693ec121d98145dbb618a09cc0b011a6f2ea4d8f5fcf',
    },
}
PUBLIC_GUARD_PREDECESSORS = (
    PUBLIC_GUARD_HISTORY,
    {'commit': 'c25dfe0dfce252bc4f71e140dd498cb8a8c6050c', 'templates': {
        'tools/resource_guard.sh': '9275b3eaa793a87174d7fddfdb3293c00a0aa56f8a41b5a7f1bf9c7ac5ccb5aa',
        'tools/block/harness/runtime-tools/resource_guard.sh': '52b20a4ccb8e951a9538723a9cf21d0854c331d41f09242609ebea4840bfdecf',
    }},
    {'commit': '1bfccdef857827ad460038972fbb80480bfa30a7', 'templates': {
        'tools/resource_guard.sh': 'ce7be67dcee1a6a612eed7a4a18f6e98f406312cd36517c04b516881655debe8',
        'tools/block/harness/runtime-tools/resource_guard.sh': '6736b1c0197c449d4c67e22cfc6465176e6fa30d1fc6eaad59ba359f92b82baf',
    }},
)



class LeafNotClosed(ValueError):
    """The compiler leaf still holds a task; its booking stays until the leaf drains.

    After an out-of-memory kill the small scope process exits first, while the
    killed compiler still frees its memory inside the leaf. The release must
    wait for that memory, so it refuses now and succeeds once the leaf drains."""


class RejectedScopeSetup(ValueError):
    """Carry cleanup evidence without authorizing a guarded workload."""

    def __init__(self, identity):
        super().__init__('The owned standalone scope lacks its writer identity.')
        self.identity = identity


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

    def slice_sample(self):
        """Sample the unchanged workload slice without granting identity authority."""
        started = time.monotonic_ns()
        before = self.directory(self.parent)
        maximum = self.slice_max()
        statistics = dict(line.split() for line in (self.parent / 'memory.stat').read_text().splitlines())
        if 'anon' not in statistics:
            raise ValueError('The live slice lacks its anonymous-memory counter.')
        current = int(statistics['anon'])
        integer(current, 'live slice memory')
        if maximum <= 0 or self.directory(self.parent) != before or self.slice_max() != maximum:
            raise ValueError('The live slice sample changed its fence or identity.')
        return {'sampled_monotonic_ns': started, 'live_bytes': current,
                'slice_max_bytes': maximum, 'counter': 'memory.stat:anon', 'scope': str(self.parent),
                'device': before[0], 'inode': before[1]}

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

    @staticmethod
    def content_identity(info):
        """Identify unchanged guard bytes across Dune cache hardlinks.

        A new hardlink changes ctime, and a cache restore can change the inode.
        The SHA-256 digest binds the content; size, mode and owner bind the file.
        """
        return (info.st_size, info.st_mode, info.st_uid)

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

    def claim(self, data, key, *, pending_shell=None):
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
                sample = self.shell(marker, owner=record['owner'],
                                    guard_attestation=record.get('guard_attestation'))
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
            staging = (kind == 'entry' and not (out / 'BATCH-PROCESS.json').exists()
                       and (out / 'STAGING-PROCESS.json').exists())
            batch = self.read(out / ('STAGING-PROCESS.json' if staging else 'BATCH-PROCESS.json'))
            if self.process(batch) != owner['pid']:
                raise ValueError('The batch process has another owner.')
            if kind == 'entry':
                if self.read(out / 'STARTED.json')['owner'] != owner:
                    raise ValueError('The entry token differs from its ledger owner.')
                if key != 'EntryChain_' + owner['block'] + '_' + owner['token']:
                    raise ValueError('The entry claim token changed.')
                identity = out / 'BATCH-IDENTITY.json'
                if not os.path.lexists(identity):
                    row = self.early_entry_scope(data, key, owner, out, batch, pending_shell)
                else:
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
            if any((self.content_identity if len(identity) == 3 else self.file_identity)(path.lstat()) != identity
                   for path, identity in self.consulted):
                raise ValueError('The claim ownership receipts changed during sampling.')
            return row
        except (OSError, ValueError, KeyError, IndexError, StopIteration, TypeError) as error:
            return {'verified': False, 'live_bytes': 0, 'reason': str(error)}

    def early_entry_scope(self, data, key, owner, out, batch, pending_shell):
        """Bind the stock guard before its inside controller can write its receipt."""
        staging = not (out / 'LAUNCH.json').exists() and (out / 'STAGING-LAUNCH.json').exists()
        launch = self.read(out / ('STAGING-LAUNCH.json' if staging else 'LAUNCH.json'))
        guard = out / 'workspace/tools/resource_guard.sh'
        owner_args = self.argv(owner)
        if (len(owner_args) != 7 or owner_args[1] != '-B'
                or Path(owner_args[2]).name != 'entry_chain_run.py'
                or owner_args[-2:] != [owner['block'], str(out)]):
            raise ValueError('The early entry controller belongs to another output.')
        inside = owner_args[:3] + ['--inside', str(out)]
        if staging:
            from staging_peaks import authenticate_launch
            expected, guard = authenticate_launch(self,launch,owner,owner_args,out,ledger_claims(data)[key])
        else:
            expected = [str(guard), 'batch', 'entry-chain-' + owner['block'], '--',
                        str(guard), 'scope', 'entry-chain-client', '--', *inside]
        if launch['owner'] != owner or launch['argv'] != expected:
            raise ValueError('The early entry launch differs from its owner.')
        wrapper = self.argv(batch)
        registry = str(guard.with_name('run_registry.py'))
        prefix = wrapper[:wrapper.index('--')]
        registry_index = prefix.index(registry)
        if (prefix[:registry_index] not in ([prefix[0]], [prefix[0], '-B'])
                or prefix[registry_index + 1:-1] != ['run', '--kind', 'stock-batch', '--owner']
                or not prefix[-1] or wrapper[len(prefix) + 1:] != expected):
            raise ValueError('The early batch wrapper belongs to another launch.')
        candidates = [(Path(record['marker']), Path(record['marker']), record)
                      for record in data.get('shell_claim_owners', {}).values()]
        if pending_shell is not None:
            candidates.insert(0, (*map(Path, pending_shell), None))
        failures = []
        for marker, token, record in candidates:
            try:
                before = self.file_identity(token.lstat())
                lines = token.read_text().splitlines()
                pairs = [line.split('=', 1) for line in lines[1:] if '=' in line]
                fields = dict(pairs)
                generation = fields['reservation_generation']
                expected_directory = Path(data.get('shell_marker_directory', marker_directory()))
                if (len(fields) != len(pairs) or marker.parent != expected_directory
                        or marker.parent.resolve() != marker.parent
                        or not re.fullmatch(r'[a-zA-Z0-9-]{16,80}', generation)
                        or marker.name.partition('.')[2] != generation):
                    raise ValueError('The early shell generation or namespace changed.')
                actor = {'pid': int(marker.name.split('.')[0]),
                         'startticks': int(fields['owner_start'])}
                if record is None:
                    if lines[0] != 'confirmed' or os.path.lexists(marker):
                        raise ValueError('The pending shell token already exists.')
                elif (record['owner'] != actor or record['generation'] != generation
                      or tuple(record['token_identity']) != before):
                    raise ValueError('The admitted shell token identity changed.')
                amount = max(int(fields['memory_claim_bytes']),
                             int(fields.get('memory_probe_claim_bytes', 0)))
                canonical = ledger_claims(data)[key]
                if fields.get('writer') != '':
                    raise ValueError('The early shell booking differs from its claim.')
                if staging:
                    authenticate_launch(self,launch,owner,owner_args,out,canonical,amount)
                elif amount != canonical:
                    from scope_bookings import authenticate_client
                    config_path = Path(owner_args[3])
                    config = self.read(config_path)
                    if hashlib.sha256(config_path.read_bytes()).hexdigest() != owner_args[4]:
                        raise ValueError('The early controller configuration changed.')
                    authenticate_client(config, owner_args[2], owner['block'], out,
                                        launch, amount, canonical)
                source = self.guard_source(fields['guard_source_path'], fields['guard_source_sha256'])
                if source['path'] != str(guard):
                    raise ValueError('The early shell uses another public guard.')
                args = self.argv(actor)
                if args not in (expected[4:], ['bash', *expected[4:]]):
                    raise ValueError('The early shell belongs to another command.')
                sample = self.shell(token, owner=actor)
                if sample.get('verified') is not True or sample.get('aggregate_verified') is not True:
                    raise ValueError('The early shell aggregate is not authenticated.')
                aggregate = Path(sample['scope'])
                creator_pid = int(re.fullmatch(
                    rf'zesuworkloads-aggregate{self.uid}p([0-9]+)r[0-9]+\.slice', aggregate.name)[1])
                raw = (self.proc / str(creator_pid) / 'stat').read_text().rsplit(')', 1)[1].split()
                creator = {'pid': creator_pid, 'startticks': int(raw[19])}
                if self.process(creator) != batch['pid']:
                    raise ValueError('The early aggregate has another batch creator.')
                if self.argv(creator) not in (expected, ['bash', *expected]):
                    raise ValueError('The early aggregate creator uses another command.')
                chain = self.ancestry(actor['pid'], creator)
                fence = int(fields['memory_fence_bytes'])
                if (fence <= 0 or fence > SLICE_MAX_BYTES
                        or int((aggregate / 'memory.max').read_text()) != fence
                        or (aggregate / 'memory.swap.max').read_text().strip() != '0'):
                    raise ValueError('The early aggregate fence changed.')
                row = self.scope(aggregate, actor, batch,
                                 expected=(sample['device'], sample['inode']))
                if (int((aggregate / 'memory.max').read_text()) != fence
                        or (aggregate / 'memory.swap.max').read_text().strip() != '0'
                        or self.directory(aggregate) != (sample['device'], sample['inode'])
                        or self.file_identity(token.lstat()) != before
                        or self.content_identity(guard.lstat()) != tuple(source['identity'])
                        or any(self.process(item) != parent for item, parent in chain)
                        or self.process(batch) != owner['pid']
                        or self.process(creator) != batch['pid']
                        or self.argv(owner) != owner_args
                        or self.argv(creator) not in (expected, ['bash', *expected])
                        or self.argv(actor) != args or self.argv(batch) != wrapper
                        or os.path.lexists(out / 'BATCH-IDENTITY.json')):
                    raise ValueError('The early entry association changed during sampling.')
                self.consulted.append((token, before))
                self.consulted.append((guard, tuple(source['identity'])))
                return dict(row, reason='authenticated early entry aggregate')
            except (OSError, ValueError, KeyError, IndexError, StopIteration, TypeError) as error:
                failures.append(str(error))
        raise ValueError('The early entry lacks an authenticated shell token: ' + '; '.join(failures))

    def residual(self, bound):
        """Sample a previously authenticated aggregate after its token ends."""
        try:
            path = Path(bound['scope'])
            if path.resolve() != path:
                raise ValueError('The retained aggregate contains an alias.')
            static = bound.get('static_until_absent') is True
            if path.parent != self.parent or (not static and not re.fullmatch(
                    rf'zesuworkloads-aggregate{self.uid}p[0-9]+r[0-9]+\.slice', path.name)):
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
            if 'populated 0' in events.splitlines() and not static:
                return {'verified': True, 'closed': True, 'live_bytes': 0}
            if 'populated 1' not in events.splitlines() and not (static and 'populated 0' in events.splitlines()):
                raise ValueError('The retained aggregate population is unknown.')
            row = dict(bound, verified=True, aggregate_verified=True, live_bytes=live,
                       reason='authenticated aggregate remains populated')
            try:
                anon = next(int(line.split()[1]) for line in
                            (path / 'memory.stat').read_text().splitlines() if line.startswith('anon '))
                if self.directory(path) == before and anon >= 0:
                    row['anon_bytes'] = anon
            except (OSError, StopIteration, ValueError, IndexError):
                pass
            return row
        except (OSError, ValueError, KeyError, TypeError) as error:
            return {'verified': False, 'live_bytes': 0, 'reason': str(error)}

    def shell(self, marker, *, owner=None, guard_attestation=None):
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
                if leaf.get('verified') is not True and guard_attestation is not None:
                    leaf = self.owned_scope(path, guard_attestation)
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

    def guard_source(self, path, expected_hash):
        """Bind one executed public guard to the helper's installed guard bytes."""
        path = Path(path)
        if not path.is_absolute() or path.resolve(strict=True) != path or path.name != 'resource_guard.sh':
            raise ValueError('The public guard source path changed.')
        before = self.content_identity(path.lstat())
        if not stat.S_ISREG(before[1]) or before[2] != self.uid or before[1] & 0o022:
            raise ValueError('The public guard source is not owned.')
        tools = next(parent for parent in Path(__file__).resolve().parents if parent.name == 'tools')
        digest = hashlib.sha256(path.read_bytes()).hexdigest()
        approved = any(digest in row['templates'].values() for row in PUBLIC_GUARD_PREDECESSORS)
        for public in (tools / 'resource_guard.sh',
                       tools / 'block/harness/runtime-tools/resource_guard.sh'):
            try:
                reference = self.content_identity(public.lstat())
                if (public.resolve(strict=True) != public or not stat.S_ISREG(reference[1])
                        or reference[2] != self.uid or reference[1] & 0o022):
                    raise ValueError('The pinned public guard is not owned.')
                approved |= digest == hashlib.sha256(public.read_bytes()).hexdigest()
                if self.content_identity(public.lstat()) != reference:
                    raise ValueError('The pinned public guard changed while reading.')
            except FileNotFoundError:
                continue  # Staged tools keep their guard beside this helper.
        if (digest != expected_hash or not approved
                or self.content_identity(path.lstat()) != before):
            raise ValueError('The public guard source bytes changed.')
        return {'path': str(path), 'sha256': digest, 'identity': list(before)}

    def guard_leaf(self, marker):
        """Check token ownership and kernel membership without compiler reuse keys."""
        marker = Path(marker)
        before = self.file_identity(marker.lstat())
        if not stat.S_ISREG(before[5]) or before[6] != self.uid or before[5] & 0o022:
            raise ValueError('The owned scope token is not private.')
        lines = marker.read_text().splitlines()
        pairs = [line.split('=', 1) for line in lines[1:] if '=' in line]
        fields = dict(pairs)
        generation = fields['reservation_generation']
        if (len(pairs) != len(fields) or not re.fullmatch(
                r'[0-9a-f]{8}-(?:[0-9a-f]{4}-){3}[0-9a-f]{12}', generation)
                or marker.name.partition('.')[2] != generation):
            raise ValueError('The owned scope generation changed.')
        owner = {'pid': int(marker.name.split('.')[0]), 'startticks': int(fields['owner_start'])}
        actor = {'pid': int(lines[0]), 'startticks': int(fields['child_start'])}
        chain = self.ancestry(actor['pid'], owner)
        relative = next(line[3:] for line in (self.proc / str(actor['pid']) / 'cgroup').read_text().splitlines()
                        if line.startswith('0::'))
        path = self.root / relative.lstrip('/')
        if not re.fullmatch(rf'zesudet-.+-{owner["pid"]}-[0-9]+\.scope', path.name):
            raise ValueError('The owned scope lacks its exact guarded leaf.')
        rejected_setup = False
        if path.parent == self.parent:
            environment = dict(item.split('=', 1) for item in
                (self.proc / str(actor['pid']) / 'environ').read_bytes().decode().split('\0') if '=' in item)
            writer = fields.get('writer', '')
            if (not re.fullmatch(r'[a-zA-Z0-9._-]+', writer) or environment.get('ZESU_WRITER_ID') != writer
                    or not path.name.startswith('zesudet-writer-' + writer + '-')):
                rejected_setup = True
            identity = self.directory(path)
            live = integer(int((path / 'memory.current').read_text()), 'owned scope memory')
            row = dict(verified=True, aggregate_verified=False, scope=str(path), device=identity[0],
                       inode=identity[1], live_bytes=live)
            if self.directory(path) != identity:
                raise ValueError('The owned standalone scope changed.')
        else:
            aggregate = next(p for p in path.parents if p.parent == self.parent)
            if aggregate.name != fields['aggregate']:
                raise ValueError('The owned scope aggregate changed.')
            creator = int(re.fullmatch(rf'zesuworkloads-aggregate{self.uid}p([0-9]+)r[0-9]+\.slice', aggregate.name)[1])
            raw = (self.proc / str(creator) / 'stat').read_text().rsplit(')', 1)[1].split()
            batch = {'pid': creator, 'startticks': int(raw[19])}
            self.ancestry(owner['pid'], batch)
            row = self.scope(path, actor, batch, leaf=True)
        if (any(self.process(item) != parent for item, parent in chain)
                or self.file_identity(marker.lstat()) != before
                or (self.proc / str(actor['pid']) / 'cgroup').read_text().splitlines() != ['0::' + relative]):
            raise ValueError('The owned scope identity changed during sampling.')
        if rejected_setup:
            raise RejectedScopeSetup((row, owner, actor, generation, before))
        return row, owner, actor, generation, before

    def scope_exec(self, marker, source):
        """Validate the public scope-exec command before it replaces its process."""
        bound = self.guard_source(source['path'], source['sha256'])
        if bound != source:
            raise ValueError('The admitted public guard identity changed.')
        rejected = None
        try:
            identity = self.guard_leaf(marker)
        except RejectedScopeSetup as error:
            rejected = error
            identity = error.identity
        row, owner, actor, generation, before = identity
        argv = self.argv(actor)
        position = 1 if argv and Path(argv[0]).name == 'bash' else 0
        if (len(argv) < position + 5 or argv[position:position + 4] !=
                [source['path'], 'scope-exec', str(marker), '--']):
            raise ValueError('The pre-exec actor is not this public scope-exec command.')
        if (self.file_identity(Path(marker).lstat()) != before or self.argv(actor) != argv
                or self.content_identity(Path(source['path']).lstat()) != tuple(source['identity'])):
            raise ValueError('The pre-exec scope changed during validation.')
        attestation = {'schema': 'owned.guard.scope.v1', 'marker': str(marker), 'generation': generation,
                       'owner': owner, 'actor': actor, 'source': source, 'scope_exec_argv': argv,
                       'leaf': {name: row[name] for name in ('scope', 'device', 'inode')}}
        if rejected is not None:
            attestation['schema'] = 'rejected.guard.setup.v1'
            attestation['token_identity'] = list(before)
            rejected.cleanup = attestation
            raise rejected
        return row, attestation

    def owned_scope(self, marker, attestation):
        """Check a post-exec scope using its sealed pre-exec attestation only."""
        try:
            source = attestation['source']
            if self.guard_source(source['path'], source['sha256']) != source:
                raise ValueError('The attested public guard identity changed.')
            row, owner, actor, generation, before = self.guard_leaf(marker)
            if (attestation['schema'] != 'owned.guard.scope.v1' or attestation['marker'] != str(marker)
                    or attestation['generation'] != generation or attestation['owner'] != owner
                    or attestation['actor'] != actor or attestation['leaf'] !=
                    {name: row[name] for name in ('scope', 'device', 'inode')}):
                raise ValueError('The owned scope differs from its pre-exec attestation.')
            environment = dict(item.split('=', 1) for item in
                (self.proc / str(actor['pid']) / 'environ').read_bytes().decode().split('\0') if '=' in item)
            if environment.get('ZESU_OWNED_GUARD_TOKEN') != str(marker):
                raise ValueError('The actor lacks its exact inner guard identity.')
            self.process(actor)
            again = self.guard_leaf(marker)
            if (self.file_identity(Path(marker).lstat()) != before or again[1:4] != (owner, actor, generation)
                    or any(again[0][name] != row[name] for name in ('scope', 'device', 'inode'))):
                raise ValueError('The owned scope token changed after environment sampling.')
            return dict(row, reason='authenticated owned scope; no compiler-slot reuse')
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
            integer(amount, 'shell booking')
            if reader.file_identity(marker.lstat()) != before:
                raise ValueError('A shell reservation changed while reading.')
            observation = reader.shell(marker)
            if (shell_key(marker) not in data.get('shell_claim_owners', {})
                    and observation.get('aggregate_verified') is True):
                try:
                    amount = legacy_aggregate_booking(reader, observation, [marker])['booking_bytes']
                except (OSError, ValueError):
                    observation = {'verified': False, 'live_bytes': 0, 'reason': 'legacy aggregate fence is unknown'}
            observation = dict(observation, legacy_aggregate_name=fields.get('aggregate', ''))
            rows[shell_key(marker)] = (amount, observation)
        except FileNotFoundError:
            raise ValueError('A shell token disappeared during the shared projection.')
    return rows


def unmeasured_shell(data, key):
    """A compile booked at its full fence has no measured claim."""
    try:
        marker = Path(data['shell_claim_owners'][key]['marker'])
        fields = dict(line.split('=', 1) for line in marker.read_text().splitlines()[1:] if '=' in line)
        return int(fields['memory_claim_bytes']) >= int(fields['memory_fence_bytes'])
    except (KeyError, OSError, ValueError, TypeError):
        return True


def sum_gate_compiles(data, claims, observations, new_observation=None, new_bytes=0, new_unmeasured=False):
    """Book a measured gate as its own claim plus its running compiles.

    Shared-aggregate grouping counts members as max(), so a gate claim had to
    cover every compile inside it: 47.3 GiB booked at a 0.55 GiB anon peak on a
    cached check-fast. A gate with a measured own claim (it records its cold
    basis in correctness_gate_cold_claims) now books own + the sum of its
    running compile claims, and at least its cold basis while any of them is
    unmeasured. An unmeasured gate keeps the max() rule.
    """
    cold_claims = data.get('correctness_gate_cold_claims', {})
    for gate, cold in cold_claims.items():
        own = claims.get(gate, 0)
        sample = observations.get(gate, {})
        if not own or sample.get('verified') is not True or sample.get('aggregate_verified') is not True:
            continue
        members = [key for key, amount in claims.items()
                   if key != gate and amount and key in data.get('shell_claim_owners', {})
                   and observations.get(key, {}).get('verified') is True
                   and observations[key].get('scope') == sample.get('scope')]
        total = own + sum(claims[key] for key in members)
        # A compile asking to start inside this gate adds to the sum too;
        # grouped with the gate it would otherwise count as max().
        joining = ((new_observation or {}).get('scope') == sample.get('scope')
                   and new_observation.get('verified') is True)
        if joining:
            total += new_bytes
        if any(unmeasured_shell(data, key) for key in members) or (joining and new_unmeasured):
            total = max(total, cold)
        claims[gate] = total
        for key in members:
            claims[key] = 0


# A refused request records itself as a waiter. After a bounded wait, every
# newer and smaller request must leave room for it, on bookings and on live
# memory, and the waiter may use the live-memory path above the small-request
# ceiling. Without this a 32 GiB slot waited indefinitely while 1-4 GiB
# requests took each gap on live memory (2026-11-11, soundness gate).
WAITERS = 'admission_waiters'


def wait_bound_ns():
    try:
        seconds = int(os.environ.get('ZESU_ADMISSION_WAIT_BOUND_S', '300'))
    except ValueError:
        seconds = 300
    return max(0, seconds) * 1_000_000_000


def record_waiter(data, key, request_bytes, owner, now_ns=None):
    """Keep the first refusal time of one request. Return True when the record changed."""
    row = data.get(WAITERS, {}).get(key)
    if row and row.get('bytes') == request_bytes and row.get('owner') == owner:
        return False
    data.setdefault(WAITERS, {})[key] = {'bytes': request_bytes, 'owner': owner,
        'since_ns': time.time_ns() if now_ns is None else now_ns}
    return True


def clear_waiter(data, key):
    return data.get(WAITERS, {}).pop(key, None) is not None


def senior_waiters(data, requester, request_bytes, reader):
    """Return (bytes this request must leave free, whether it is itself an aged waiter)."""
    now, bound = time.time_ns(), wait_bound_ns()
    waiters = data.get(WAITERS, {})
    own = waiters.get(requester) if requester is not None else None
    since = own['since_ns'] if own else now
    reserved = 0
    for key, row in list(waiters.items()):
        if key == requester:
            continue
        try:
            reader.process(row['owner'])
        except (AttributeError, KeyError, OSError, TypeError, ValueError):
            del waiters[key]  # A dead or unreadable waiter holds nothing.
            continue
        if now - row['since_ns'] >= bound and row['since_ns'] < since and row['bytes'] > request_bytes:
            reserved += row['bytes']
    return reserved, bool(own) and now - since >= bound


def projection(data, claims, new_bytes, available_bytes, *, reader=None, new_observation=None,
               pending_shell=None, requester=None):
    reader = ScopeReader() if reader is None else reader
    claims = dict(claims)
    observations = {}
    for key, amount in claims.items():
        if amount:
            options = {'pending_shell': pending_shell} if (pending_shell is not None
                and key in data.get('entry_pilot_outside_owners', {})) else {}
            observations[key] = reader.claim(data, key, **options)
    # A reviewed static view changes accounting only. It grants no token or slot.
    static_names = set()
    for key, hold in data.get('legacy_kernel_accounts', {}).items():
        bound = hold['aggregate']
        sample = reader.residual(dict(bound, static_until_absent=True))
        if sample.get('closed') is True:
            static_names.add(Path(bound['scope']).name)
            continue
        amount = hold['booking_bytes']
        integer(amount, 'reviewed static booking')
        for prior, expected_owner in hold.get('canonical_owners', {}).items():
            actual = data.get('entry_pilot_outside_owners', {}).get(prior) or data.get('correctness_gate_owners', {}).get(prior)
            if (not isinstance(expected_owner, dict) or not {'pid', 'startticks'} <= expected_owner.keys()
                    or not actual or any(actual.get(name) != value for name, value in expected_owner.items())):
                raise ValueError('The static canonical association changed.')
            if sample.get('verified') is True:
                amount = max(amount, claims.pop(prior, 0))
                observations.pop(prior, None)
            for name in ('entry_pilot_outside_releases', 'correctness_gate_releases'):
                released = data.get(name, {}).get(prior, {})
                amount = max(amount, released.get('bytes', 0))
        claims[key] = amount
        observations[key] = sample
        if sample.get('verified') is True:
            static_names.add(Path(bound['scope']).name)
    # Legacy writers stay visible until rollout closes or updates them.
    # Non-kernel unit readers supply their own inventory explicitly.
    if isinstance(reader, ScopeReader) and (reader.proc == PROC or 'shell_marker_directory' in data):
        for key, (amount, observation) in shell_rows(data, reader).items():
            if key not in data.get('shell_claim_owners', {}) and observation.get('legacy_aggregate_name') in static_names:
                continue
            claims[key] = max(claims.get(key, 0), amount)
            if key not in data.get('shell_claim_owners', {}):
                observations[key] = observation
    retained_groups = dict(data.get('legacy_aggregate_holds', {}))
    shell_holds = data.get('shell_aggregate_holds', {})
    retained_groups.update(shell_holds)
    for key, retained in retained_groups.items():
        sample = reader.residual(retained['aggregate'])
        if sample.get('closed') is True:
            continue
        # An unknown retained scope keeps its last booking. A verified live
        # aggregate contributes actual usage even after its final token ends:
        # its live anonymous memory plus the bookings of its compiles that
        # still run. Without this a batch kept the largest claim it ever
        # released until it ended (55 holds, 298.8 GiB on 2026-11-10).
        claims[key] = retained['fallback_bytes']
        if (key in shell_holds and sample.get('aggregate_verified') is True
                and type(sample.get('anon_bytes')) is int):
            running = sum(amount for other, amount in claims.items()
                          if other != key and amount
                          and observations.get(other, {}).get('verified') is True
                          and observations[other].get('scope') == sample.get('scope'))
            claims[key] = min(retained["fallback_bytes"], sample["anon_bytes"] + running)
        observations[key] = sample
    new_unmeasured = False
    if pending_shell is not None:
        try:
            fields = dict(line.split('=', 1) for line in Path(pending_shell[1]).read_text().splitlines()[1:] if '=' in line)
            new_unmeasured = int(fields['memory_claim_bytes']) >= int(fields['memory_fence_bytes'])
        except (KeyError, OSError, ValueError, TypeError, IndexError):
            new_unmeasured = True
    sum_gate_compiles(data, claims, observations, new_observation, new_bytes, new_unmeasured)
    reserved, senior = senior_waiters(data, requester, new_bytes, reader)
    if reserved:
        claims['admission_waiters'] = reserved
    result = dict(evaluate(claims, new_bytes, available_bytes, observations=observations,
                           new_observation=new_observation,
                           slice_max_bytes=reader.slice_max()),
                  admission_pool='canonical', memory_ledger='unified', admission_basis='booking',
                  waiter_reserved_bytes=reserved, senior_waiter=senior)
    return live_memory_admission(result, reader, reserved_bytes=reserved, senior=senior)


def live_memory_admission(result, reader, *, reserved_bytes=0, senior=False):
    """Permit a small request below half of the freshly verified slice cap.

    The caller still owns compiler slots, worker limits, and claim publication.
    This decision never changes a booking, scope fence, or termination watch.
    An aged waiter may exceed the small-request ceiling; every other request
    leaves the reserved bytes of older, larger aged waiters free.
    """
    request = result['new_claim_bytes']
    try:
        ceiling = int(os.environ.get('ZESU_LIVE_REQUEST_LIMIT_GIB', '16'))
        if not 1 <= ceiling <= 175:
            return result
    except ValueError:
        return result
    if not 0 < request <= (result['slice_max_bytes'] if senior else ceiling * GIB):
        return result
    try:
        sample = reader.slice_sample()
        age = time.monotonic_ns() - sample['sampled_monotonic_ns']
        live, maximum = sample['live_bytes'], sample['slice_max_bytes']
        integer(live, 'live slice memory')
        integer(maximum, 'sampled slice maximum')
        if (type(sample['sampled_monotonic_ns']) is not int or not 0 <= age <= 10_000_000_000
                or maximum <= 0 or maximum != result['slice_max_bytes']):
            return result
    except (AttributeError, KeyError, OSError, TypeError, ValueError):
        return result
    result['live_memory_sample'] = dict(sample, age_ns=age)
    # MemAvailable remains an independent host-pressure check. All existing
    # booking totals remain visible even when the small-request path is used.
    if live + request + reserved_bytes <= maximum // 2 and request <= result['budget_bytes']:
        result.update(fits=True, admitted=True, admission_basis='live_memory')
        print('live-memory admission: live_bytes=' + str(live)
              + ' request_bytes=' + str(request)
              + ' booked_bytes=' + str(result['active_claim_bytes'])
              + ' slice_max_bytes=' + str(maximum), file=sys.stderr)
    return result


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


def legacy_aggregate_booking(reader, observation, markers):
    """Use approved token bookings once, or the bounded inner-scope fallback."""
    if observation.get('verified') is not True or observation.get('aggregate_verified') is not True:
        raise ValueError('The legacy booking lacks an authenticated aggregate.')
    path = Path(observation['scope'])
    fence = aggregate_fence(reader, observation)
    recorded = []
    for marker in dict.fromkeys(map(Path, markers)):
        before = reader.file_identity(marker.lstat())
        if marker.lstat().st_uid != reader.uid or marker.lstat().st_mode & 0o022:
            raise ValueError('The legacy booking token is not owned.')
        sample = reader.shell(marker)
        if (sample.get('verified') is not True or sample.get('aggregate_verified') is not True
                or any(sample.get(name) != observation.get(name) for name in ('scope', 'device', 'inode'))):
            raise ValueError('The legacy booking token belongs to another aggregate.')
        fields = dict(line.split('=', 1) for line in marker.read_text().splitlines()[1:] if '=' in line)
        values = [int(fields[name]) for name in ('memory_claim_bytes', 'memory_probe_claim_bytes') if name in fields]
        for value in values:
            integer(value, 'recorded legacy booking')
            if value == 0:
                raise ValueError('A recorded legacy booking is zero.')
        if values:
            recorded.append(max(values))
        if reader.file_identity(marker.lstat()) != before:
            raise ValueError('The legacy booking token changed during sampling.')
    if recorded:
        amount = max(recorded)
        return {'booking_bytes': amount, 'recorded_booking_bytes': amount,
                'origin': 'recorded approved shell tokens'}
    children = sorted(child for child in path.iterdir() if child.name.endswith('.scope'))
    if not children:
        raise ValueError('The legacy aggregate has no bounded inner scope.')
    total = 0
    identities = []
    for child in children:
        before = reader.directory(child)
        maximum = (child / 'memory.max').read_text().strip()
        amount = fence if maximum == 'max' else int(maximum)
        integer(amount, 'inner scope fence')
        if (child / 'memory.swap.max').read_text().strip() != '0':
            raise ValueError('An inner legacy scope has an unknown swap fence.')
        total += amount
        identities.append((child, before, maximum))
    if (sorted(child for child in path.iterdir() if child.name.endswith('.scope')) != children
            or any(reader.directory(child) != before or (child / 'memory.max').read_text().strip() != maximum
                   for child, before, maximum in identities)):
        raise ValueError('The inner legacy scope inventory changed.')
    aggregate_fence(reader, observation)
    return {'booking_bytes': min(fence, total), 'recorded_booking_bytes': None,
            'origin': 'minimum aggregate fence and summed inner fences'}


def canonical_guard_fence(data, guard_pid, *, reader=None):
    """Authorize a new aggregate through the exact live canonical owner."""
    reader = ScopeReader() if reader is None else reader
    raw = (reader.proc / str(guard_pid) / 'stat').read_text().rsplit(')', 1)[1].split()
    actor = {'pid': guard_pid, 'startticks': int(raw[19])}
    reader.process(actor)
    argv = reader.argv(actor)
    position = 0 if Path(argv[0]).name == 'resource_guard.sh' else 1
    if (position >= len(argv) or Path(argv[position]).name != 'resource_guard.sh'
            or position == 1 and Path(argv[0]).name not in ('bash', 'sh', 'dash')
            or argv[position + 1:position + 2] != ['batch']):
        raise ValueError('The aggregate requester is not the exact stock batch guard.')
    matches = []
    for key, bound in data.get('claim_fences', {}).items():
        if not data.get('fixed_claims', {}).get(key, 0):
            continue
        owner = bound['owner']
        kind = ('gate' if data.get('correctness_gate_owners', {}).get(key) == owner else
                'entry' if data.get('entry_pilot_outside_owners', {}).get(key) == owner else None)
        if kind is None:
            raise ValueError('The canonical fence owner differs from its claim.')
        try:
            chain = reader.ancestry(guard_pid, owner)
        except (OSError, ValueError):
            continue
        if any(reader.process(item) != parent for item, parent in chain):
            raise ValueError('The aggregate requester ancestry changed.')
        matches.append((kind, bound['physical_fence_bytes']))
    if len(matches) > 1:
        raise ValueError('The aggregate requester has ambiguous canonical owners.')
    return matches[0] if matches else (None, None)


def select_guard_aggregate_limit(guard_pid, inner_fence_bytes, booking_bytes, *,
                                 explicit_limit_bytes=None, gate_limit_bytes=None,
                                 ledger=None, reader=None):
    ledger = Path(ledger or os.environ.get('ZESU_CANONICAL_LEDGER', DEFAULT_LEDGER))
    with ledger_transaction(ledger) as data:
        kind, bound = canonical_guard_fence(data, guard_pid, reader=reader)
        if kind is None:
            if explicit_limit_bytes is not None or gate_limit_bytes is not None:
                raise ValueError('A plain shell request cannot use an unreviewed aggregate override.')
            return new_aggregate_limit(inner_fence_bytes, booking_bytes)
        if (explicit_limit_bytes is not None and explicit_limit_bytes != bound
                or gate_limit_bytes is not None and (kind != 'gate' or gate_limit_bytes != bound)):
            raise ValueError('The aggregate override differs from its canonical fence.')
        return new_aggregate_limit(inner_fence_bytes, booking_bytes,
                                   gate_limit_bytes=bound if kind == 'gate' else None,
                                   explicit_limit_bytes=bound if kind == 'entry' else None)


def new_aggregate_limit(inner_fence_bytes, booking_bytes, *, explicit_limit_bytes=None, gate_limit_bytes=None):
    """Select a new fence. Explicit limits require canonical authorization upstream."""
    for value in (inner_fence_bytes, booking_bytes, explicit_limit_bytes, gate_limit_bytes):
        if value is not None:
            integer(value, 'new aggregate limit')
            if value == 0 or value > SLICE_MAX_BYTES:
                raise ValueError('The new aggregate limit is outside the workload parent.')
    if explicit_limit_bytes is not None and gate_limit_bytes is not None and explicit_limit_bytes != gate_limit_bytes:
        raise ValueError('The explicit canonical and gate fences disagree.')
    return explicit_limit_bytes or gate_limit_bytes or max(inner_fence_bytes, booking_bytes)


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
        position = positions[0]
        if position != 0 and not (position == 1 and Path(argv[0]).name in ('bash', 'sh', 'dash')):
            raise ValueError('The public guard is not the executable script.')
        mode = argv[positions[0] + 1] if positions[0] + 1 < len(argv) else None
        if mode not in ('scope', 'scope-exec', 'batch'):
            raise ValueError('An old writer can create an unrepresented aggregate.')
        token_owner = writer.get('token_owner', owner)
        if mode != 'batch' and token_owner != owner:
            raise ValueError('A scope writer cannot use another token owner.')
        if int(Path(writer['marker']).name.split('.')[0]) != token_owner['pid']:
            raise ValueError('The legacy token filename names another owner.')
        reader.process(token_owner)
        observation = reader.shell(writer['marker'], owner=token_owner)
        if observation.get('aggregate_verified') is not True:
            raise ValueError('The old writer has no authenticated aggregate.')
        path = Path(observation['scope'])
        chain = []
        if mode == 'batch':
            if re.fullmatch(rf'zesuworkloads-aggregate{reader.uid}p{owner["pid"]}r[0-9]+\.slice', path.name) is None:
                raise ValueError('The old batch has not created its exact aggregate.')
            if token_owner != owner:
                chain = reader.ancestry(token_owner['pid'], owner)
        else:
            environment = dict(item.split('=', 1) for item in
                (reader.proc / str(owner['pid']) / 'environ').read_bytes().decode().split('\0') if '=' in item)
            if environment.get('ZESU_AGGREGATE_SLICE') != path.name:
                raise ValueError('The old scope can create an unrepresented aggregate.')
        booking = legacy_aggregate_booking(reader, observation, [writer['marker']])
        identity = f"{path}:{observation['device']}:{observation['inode']}"
        key = 'legacy-aggregate:' + hashlib.sha256(identity.encode()).hexdigest()
        previous = holds.get(key, data.get('legacy_aggregate_holds', {}).get(key, {}))
        recorded = [value for value in (previous.get('recorded_booking_bytes'), booking['recorded_booking_bytes']) if value is not None]
        amount = max(recorded) if recorded else max(previous.get('fallback_bytes', 0), booking['booking_bytes'])
        holds[key] = {'aggregate': {name: observation[name] for name in ('scope', 'device', 'inode')},
                      'fallback_bytes': amount, 'recorded_booking_bytes': max(recorded) if recorded else None,
                      'booking_origin': booking['origin'], 'writer': owner, 'token_owner': token_owner, 'source': source}
        reader.process(owner)
        reader.process(token_owner)
        if any(reader.process(actor) != parent for actor, parent in chain):
            raise ValueError('The batch/token owner ancestry changed during sampling.')
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


TEST_CONTEXT_ENV = 'PYTHON_TEST_CONTEXT'


def test_process():
    """Recognize test runners even when a child removes inherited flags."""
    if os.environ.get(TEST_CONTEXT_ENV) == '1':
        return True
    if 'unittest' in sys.modules or 'pytest' in sys.modules or os.environ.get('PYTEST_CURRENT_TEST'):
        os.environ[TEST_CONTEXT_ENV] = '1'
        return True
    pid = os.getpid()
    for _ in range(128):
        try:
            process = Path('/proc') / str(pid)
            arguments = (process / 'cmdline').read_bytes().decode().split('\0')
            fields = (process / 'stat').read_text().rsplit(')', 1)[1].split()
        except (OSError, UnicodeError):
            return False
        names = [Path(value).name.lower() for value in arguments if value]
        if (any(name in {'unittest', 'pytest', 'py.test'} for name in names)
                or any(name.startswith('test_') and name.endswith('.py') for name in names)):
            os.environ[TEST_CONTEXT_ENV] = '1'
            return True
        parent = int(fields[1])
        if parent <= 1 or parent == pid:
            return False
        pid = parent
    raise ValueError('The test ancestry exceeds the supported process depth.')


# Propagate embedded runners before their children can hide the runner argv.
# This restrictive marker survives fixture cleanup of ZESU control options.
test_process()


def check_test_ledger(ledger=None):
    """Tests may use private ledgers; live accounting needs explicit consent."""
    ledger = Path(ledger or os.environ.get('ZESU_CANONICAL_LEDGER', DEFAULT_LEDGER))
    live = ledger.resolve() == DEFAULT_LEDGER.resolve()
    if not live and ledger.exists() and DEFAULT_LEDGER.exists():
        live = ledger.samefile(DEFAULT_LEDGER)
    if live and test_process() and os.environ.get('ZESU_TEST_ALLOW_LIVE_LEDGER') != '1':
        raise ValueError('Tests refuse the live ledger without explicit live mode.')


_ledger_transaction = ContextVar("admission_ledger_transaction", default=None)


@contextmanager
def ledger_transaction(ledger):
    check_test_ledger(ledger)
    ledger = Path(ledger)
    active = _ledger_transaction.get()
    if active is not None and active[0] == ledger.absolute():
        yield active[1]
        return
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
        data = json.loads(ledger.read_text())
        token = _ledger_transaction.set((ledger.absolute(), data))
        try:
            yield data
        finally:
            _ledger_transaction.reset(token)


def archived_shell_digest(data, key, ledger):
    """A released token's archive digest; the archive module is optional in fixtures."""
    if key in data.get('shell_archive', {}):
        return data['shell_archive'][key]
    try:
        import ledger_archive
    except ImportError:
        return None
    return ledger_archive.archived_shell_digest(data, key, ledger)


def active_ledger():
    active = _ledger_transaction.get()
    return active[0] if active is not None else None


def write_ledger(path, data):
    check_test_ledger(path)
    path = Path(path)
    try:
        import ledger_archive
    except ImportError:
        ledger_archive = None
    if ledger_archive is not None and ledger_archive.due(path, data):
        # Closed records leave the hot file before it is rewritten.
        ledger_archive.compact(path, data, ScopeReader(), ended_process)
    fd, name = tempfile.mkstemp(prefix='.LEDGER.', dir=path.parent)
    try:
        with os.fdopen(fd, 'w') as stream:
            # One write: json.dump issues one call per token (0.16 s against
            # 0.04 s for 17.5 MB), and every caller holds the guard mutex.
            stream.write(json.dumps(data, separators=(",", ":")) + '\n')
            stream.flush(); os.fsync(stream.fileno())
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


def prune_closed_aggregate_holds(data, reader):
    """Drop retained shell aggregates whose cgroup no longer exists.

    A removed cgroup cannot return with its recorded identity, and projection
    counts it as zero. Without pruning, every admission re-samples each hold
    ever recorded under the global guard mutex (4,228 of 4,250 on 2026-11-09).
    """
    holds = data.get('shell_aggregate_holds', {})
    for key in [key for key, hold in holds.items()
                if not Path(hold['aggregate']['scope']).exists()
                and not Path(hold['aggregate']['scope']).is_symlink()
                and reader.residual(hold['aggregate']).get('closed') is True]:
        del holds[key]


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
    guard_source = None
    if 'guard_source_path' in fields or 'guard_source_sha256' in fields:
        guard_source = reader.guard_source(fields['guard_source_path'], fields['guard_source_sha256'])
    key = shell_key(marker)
    with ledger_transaction(ledger) as data:
        if (marker.exists() or marker.is_symlink() or key in data.get('shell_claim_owners', {})
                or key in data.get('shell_archive', {})):
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
                            reader=reader, new_observation=observation,
                            pending_shell=(marker, replacement), requester=key)
        if not result['fits']:
            # The guard retries the same marker, so the first refusal dates the wait.
            if record_waiter(data, key, request_bytes, owner):
                write_ledger(ledger, data)
            return result
        clear_waiter(data, key)
        reader.process(owner)
        if reader.file_identity(replacement.lstat()) != replacement_identity:
            raise ValueError('The pending shell token changed.')
        # Publish the booking first. An interrupted token publication cannot underbook.
        data['fixed_claims'][key] = request_bytes
        data.setdefault('shell_claim_owners', {})[key] = {'owner': owner, 'marker': str(marker),
            'aggregate': observation if observation.get('aggregate_verified') is True else None,
            'generation': generation}
        if guard_source is not None:
            data['shell_claim_owners'][key]['guard_source'] = guard_source
        # Keep the decision and its totals; the per-claim observations were
        # 35 kB per live token in the hot ledger.
        data.setdefault('shell_admissions', {})[key] = {
            name: value for name, value in result.items() if name != 'claim_observations'}
        prune_closed_aggregate_holds(data, reader)
        write_ledger(ledger, data)
        os.replace(replacement, marker)
        data['shell_claim_owners'][key]['token_identity'] = reader.file_identity(marker.lstat())
        write_ledger(ledger, data)
        return result


def authorized_shell_booking(marker, amount, *, ledger=None, reader=None):
    """Return only a live token's exact, already admitted canonical booking."""
    ledger = Path(ledger or os.environ.get('ZESU_CANONICAL_LEDGER', DEFAULT_LEDGER))
    reader = ScopeReader() if reader is None else reader
    integer(amount, 'recorded shell booking')
    if not amount:
        return None
    with ledger_transaction(ledger) as data:
        key = shell_key(marker)
        record = data.get('shell_claim_owners', {}).get(key)
        if (record is None or record['marker'] != str(Path(marker).absolute())
                or data.get('fixed_claims', {}).get(key) != amount):
            return None
        sample = reader.claim(data, key)
        return amount if sample.get('verified') is True else None


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
        source = record.get('guard_source')
        actor = {'pid': int(lines[0]), 'startticks': int(fields['child_start'])}
        argv = reader.argv(actor) if source is not None else []
        position = 1 if argv and Path(argv[0]).name == 'bash' else 0
        if source is not None and argv[position:position + 2] == [source['path'], 'scope-exec']:
            try:
                sample, attestation = reader.scope_exec(marker, source)
            except RejectedScopeSetup as error:
                cleanup = error.cleanup
                if cleanup['owner'] != record['owner'] or cleanup['generation'] != record['generation']:
                    raise ValueError('The rejected setup differs from its admitted owner.')
                if reader.file_identity(marker.lstat()) != tuple(cleanup['token_identity']):
                    raise ValueError('The rejected setup token changed before publication.')
                # Retain the full claim until this exact failed setup leaf closes.
                # This receipt grants no compiler or owned-scope permission.
                record['setup_failure'] = cleanup
                record['leaf'] = cleanup['leaf']
                record['token_identity'] = cleanup['token_identity']
                write_ledger(ledger, data)
                raise
            record['guard_attestation'] = attestation
        else:
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


def ended_process(reader, actor):
    """Require the exact actor to end, including its possible zombie state."""
    if (type(actor.get('pid')) is not int or actor['pid'] <= 0 or
            type(actor.get('startticks')) is not int or actor['startticks'] <= 0):
        raise ValueError('The ended actor identity is invalid.')
    path = reader.proc / str(actor['pid'])
    try:
        fields = (path / 'stat').read_text().rsplit(')', 1)[1].split()
        return int(fields[19]) != actor['startticks'] or fields[0] in ('Z', 'X', 'x')
    except FileNotFoundError:
        return True


def _shell_recovery_record(data, key, reader):
    record = data.get('shell_claim_owners', {}).get(key)
    released = data.get('shell_releases', {}).get(key)
    if record is None and archived_shell_digest(data, key, active_ledger()) is not None:
        from shell_archive import released_records
        record, released = released_records(data, key, reader)
        return record, released, True
    return record, released, False


def recover_dead_shell(marker, *, ledger=None, reader=None):
    """Keep exact recovery or audit complete absence after interrupted publication."""
    marker = Path(marker).absolute()
    ledger = Path(ledger or os.environ.get('ZESU_CANONICAL_LEDGER', DEFAULT_LEDGER))
    reader = ScopeReader() if reader is None else reader
    with ledger_transaction(ledger) as data:
        key = shell_key(marker)
        admitted, released, was_archived = _shell_recovery_record(data, key, reader)
        archived = admitted if was_archived else None
        if was_archived and (data['fixed_claims'].get(key, 0) != 0
                or released['owner'] != admitted['owner'] or released['marker'] != admitted['marker']):
            raise ValueError('The archived token lacks exact released ownership.')
        if admitted is not None:
            lines = marker.read_text().splitlines()
            fields = dict(line.split('=', 1) for line in lines[1:] if '=' in line)
            if (fields.get('reservation_generation') != admitted.get('generation')
                    or int(fields['owner_start']) != admitted['owner']['startticks']):
                raise ValueError('The release owner differs from its token.')
            leaf = admitted.get('leaf')
            leaf_complete = isinstance(leaf, dict) and {'scope', 'device', 'inode'} <= leaf.keys()
            # A confirmed token without an authenticated aggregate cannot close
            # through release_shell. Such a record takes the absence audit below.
            complete = (bool(admitted.get('token_identity'))
                        and (lines[0] == 'confirmed' and bool(admitted.get('aggregate'))
                             or leaf_complete and fields.get('child_start')))
            if complete:
                return release_shell(marker, ledger=ledger, reader=reader, require_dead_owner=True)

        expected = Path(data.get('shell_marker_directory', marker_directory()))
        if (marker.parent != expected or marker.parent.resolve() != marker.parent
                or not re.fullmatch(r'[0-9]+\.[a-zA-Z0-9.-]+', marker.name)):
            raise ValueError('The orphan token is outside its owned namespace.')
        info = marker.lstat()
        if (not stat.S_ISREG(info.st_mode) or info.st_uid != reader.uid or info.st_mode & 0o022):
            raise ValueError('The orphan token is not private.')
        identity = reader.file_identity(info)
        raw = marker.read_bytes()
        lines = raw.decode().splitlines()
        fields = dict(line.split('=', 1) for line in lines[1:] if '=' in line)
        owner = {'pid': int(marker.name.split('.')[0]), 'startticks': int(fields['owner_start'])}
        integer(owner['pid'], 'orphan owner PID')
        integer(owner['startticks'], 'orphan owner start')
        actor = int(lines[0]) if lines[0].isdecimal() else None
        if owner['pid'] <= 0 or owner['startticks'] <= 0 or actor is not None and actor <= 0:
            raise ValueError('The orphan token has an invalid process identity.')
        if lines[0] != 'confirmed' and actor is None:
            raise ValueError('The orphan token has no exact actor state.')
        pids = [owner['pid']] + ([actor] if actor is not None else [])
        if admitted is not None:
            pids.append(integer(admitted['owner']['pid'], 'admitted owner PID'))
            for field in ('guard_attestation', 'setup_failure'):
                bound_actor = admitted.get(field, {}).get('actor')
                if bound_actor is not None:
                    pids.append(integer(bound_actor['pid'], 'admitted actor PID'))
        if any((reader.proc / str(pid)).exists() for pid in pids):
            raise ValueError('The orphan token owner or actor is still present.')
        units = [fields[name] for name in ('scope', 'aggregate') if fields.get(name)]
        if admitted is not None:
            for field in ('aggregate', 'leaf'):
                bound = admitted.get(field)
                if bound is not None:
                    path = Path(bound['scope'])
                    if not path.is_relative_to(reader.parent) or path != path.resolve():
                        raise ValueError('The admitted recovery scope is outside its owned slice.')
                    units.append(path.name)
        units = list(dict.fromkeys(units))
        writer = fields.get('writer', '')
        if not units and lines[0] == 'confirmed' and re.fullmatch(r'[a-zA-Z0-9._-]+', writer or ''):
            # A writer confirmed its slot and died before systemd created its
            # scope. Every writer scope name carries the owner PID, so absence
            # of any such scope proves no compiler ran for this token.
            if any(reader.parent.rglob(f'*-writer-{writer}-*-{owner["pid"]}-*')):
                raise ValueError('The orphan writer token still has a scope.')
            units = [f'writer-{writer}-*-{owner["pid"]}-*']
        elif not units:
            raise ValueError('The orphan token lacks its recorded scope.')
        for unit in units:
            if unit.startswith('writer-') and '*' in unit:
                continue
            if (not re.fullmatch(r'[a-zA-Z0-9_.@:-]+\.(scope|slice)', unit)
                    or any(reader.parent.rglob(unit))):
                raise ValueError('The orphan token scope is still present or invalid.')
        # A stale-owner release records the token it observed. A leftover
        # token with that exact identity is the released token itself.
        known = {tuple(archived.get('token_identity', ()))} if archived is not None else set()
        if archived is not None and released.get('observed_token_identity'):
            known.add(tuple(released['observed_token_identity']))
        if archived is not None and (archived['owner'] != owner or archived['marker'] != str(marker)
                or identity not in known):
            raise ValueError('The archived released token identity changed.')
        if reader.file_identity(marker.lstat()) != identity:
            raise ValueError('The orphan token changed during recovery.')
        audit = {'marker': str(marker), 'owner': owner, 'actor_pid': actor,
                 'absent_scope_names': units, 'token_sha256': hashlib.sha256(raw).hexdigest(),
                 'token_identity': list(identity), 'recovered_ns': time.time_ns(),
                 'route': ('archived_release' if was_archived else
                           'admitted_absence' if admitted is not None else 'unadmitted_orphan'),
                 'verified_absent_pids': pids}
        data.setdefault('shell_recovery_audits', {})[key] = audit
        if key in data['fixed_claims']:
            data['fixed_claims'][key] = 0
        if admitted is not None and not was_archived:
            data.setdefault('shell_releases', {})[key] = {
                'marker': str(marker), 'owner': admitted['owner'],
                'dead_owner_recovery': True, 'absence_only': True}
            _archive_shell_release(ledger, data, key, reader)
        prune_closed_aggregate_holds(data, reader)
        write_ledger(ledger, data)
        marker.unlink()
        return True


def recover_stale_shell(marker, *, ledger=None, reader=None):
    """Audit a stale booking only after its owner and every recorded scope end.

    A missing or replaced marker supplies no authority. The ledger supplies the
    owner and scope identities. This command never removes a replacement marker.
    """
    marker = Path(marker).absolute()
    ledger = Path(ledger or os.environ.get('ZESU_CANONICAL_LEDGER', DEFAULT_LEDGER))
    reader = ScopeReader() if reader is None else reader
    with ledger_transaction(ledger) as data:
        key = shell_key(marker)
        record, released, was_archived = _shell_recovery_record(data, key, reader)
        if record is None or record.get('marker') != str(marker):
            raise ValueError('Stale recovery requires a recorded shell owner.')
        if released is not None:
            return False
        def identity():
            try:
                return reader.file_identity(marker.lstat())
            except FileNotFoundError:
                return None
        token = identity()
        if token is not None and token == tuple(record.get('token_identity', ())):
            raise ValueError('Stale recovery requires a missing or changed token.')
        scopes = {}
        actors = [record['owner']]
        def collect(value):
            if isinstance(value, dict):
                if all(name in value for name in ('scope', 'device', 'inode')):
                    scopes[value['scope']] = value
                if isinstance(value.get('actor'), dict):
                    actors.append(value['actor'])
                for child in value.values():
                    collect(child)
            elif isinstance(value, list):
                for child in value:
                    collect(child)
        collect(record)
        def check_closed():
            for actor in actors:
                if not ended_process(reader, actor):
                    raise ValueError('The stale shell owner or actor is still live.')
            for scope, bound in scopes.items():
                Path(scope).relative_to(reader.root)
                if not leaf_closed(reader, bound):
                    raise ValueError('The stale shell scope or leaf is still populated.')
            relatives = [str(Path(scope).relative_to(reader.root)) for scope in scopes]
            owner_pid = str(record['owner']['pid'])
            for process in reader.proc.iterdir():
                if not process.name.isdigit():
                    continue
                try:
                    memberships = (process / 'cgroup').read_text().splitlines()
                except FileNotFoundError:
                    continue
                for membership in memberships:
                    location = membership.split(':', 2)[-1].lstrip('/')
                    parts = Path(location).parts
                    owned_name = any(('-' + owner_pid + '-') in part or
                                     ('p' + owner_pid + 'r') in part for part in parts)
                    if owned_name or any(location == scope or location.startswith(scope + '/')
                                         for scope in relatives):
                        raise ValueError('A process still uses the stale shell cgroup.')
        check_closed()
        amount = data.get('fixed_claims', {}).get(key, 0)
        if identity() != token:
            raise ValueError('The stale token changed during recovery.')
        check_closed()
        data.setdefault('fixed_claims', {})[key] = 0
        data.setdefault('shell_releases', {})[key] = {
            'marker': str(marker), 'owner': record['owner'],
            'stale_owner_recovery': True, 'released_bytes': amount,
            'previous_token_identity': record.get('token_identity'),
            'observed_token_identity': token, 'closed_scopes': sorted(scopes),
            'recovered_ns': time.time_ns()}
        _archive_shell_release(ledger, data, key, reader)
        write_ledger(ledger, data)
        return True


def recover_stale_shells(*, ledger=None, reader=None):
    """Find stale bookings even when an older guard removed their markers."""
    ledger = Path(ledger or os.environ.get('ZESU_CANONICAL_LEDGER', DEFAULT_LEDGER))
    reader = ScopeReader() if reader is None else reader
    with ledger_transaction(ledger) as data:
        records = [(key, record) for key, record in data.get('shell_claim_owners', {}).items()
                   if key not in data.get('shell_releases', {})
                   and data.get('fixed_claims', {}).get(key, 0) > 0]
    results = []
    for key, record in records:
        try:
            if not ended_process(reader, record['owner']):
                continue
            marker = Path(record['marker'])
            if marker.exists() and reader.file_identity(marker.lstat()) == tuple(record.get('token_identity', ())):
                continue
            released = recover_stale_shell(marker, ledger=ledger, reader=reader)
            results.append({'key': key, 'released': released})
        except (OSError, ValueError) as error:
            results.append({'key': key, 'released': False, 'reason': str(error)})
    return results


SHELL_ARCHIVE_THRESHOLD_BYTES = 16 * 1024 * 1024


def _archive_shell_release(ledger, data, key, reader):
    from shell_archive import _archive_released_record, compact_released_shells
    directory = data.get('shell_archive_directory', Path(ledger).parent/'released-shell-archive')
    _archive_released_record(data, key, directory)
    if Path(ledger).stat().st_size > SHELL_ARCHIVE_THRESHOLD_BYTES:
        compact_released_shells(data, directory, reader)


def release_shell(marker, *, ledger=None, reader=None, require_dead_owner=False):
    """Release an authenticated token whose recorded compiler actor ended."""
    marker = Path(marker).absolute()
    ledger = Path(ledger or os.environ.get('ZESU_CANONICAL_LEDGER', DEFAULT_LEDGER))
    reader = ScopeReader() if reader is None else reader
    with ledger_transaction(ledger) as data:
        key = shell_key(marker)
        record, released, was_archived = _shell_recovery_record(data, key, reader)
        if record is None:
            if require_dead_owner:
                raise ValueError('Dead-owner recovery requires an admitted shell owner.')
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
        if require_dead_owner and not ended_process(reader, record['owner']):
            raise ValueError('The shell reservation owner is still live.')
        token_identity = reader.file_identity(marker.lstat())
        if tuple(record.get('token_identity', ())) != token_identity and not require_dead_owner:
            raise ValueError('The released token identity changed.')
        lines = marker.read_text().splitlines()
        fields = dict(line.split('=', 1) for line in lines[1:] if '=' in line)
        if (fields.get('reservation_generation') != record['generation']
                or int(fields['owner_start']) != record['owner']['startticks']):
            raise ValueError('The release owner differs from its token.')
        if released and data.get('fixed_claims', {}).get(key) == 0:
            if released.get('owner') != record['owner'] or released.get('marker') != str(marker):
                raise ValueError('The released marker differs from its ledger record.')
            if reader.file_identity(marker.lstat()) != token_identity:
                raise ValueError('The released marker changed during cleanup.')
            marker.unlink()
            cleanup = {'observed_token_identity': token_identity, 'removed_ns': time.time_ns()}
            if was_archived:
                data.setdefault('shell_recovery_audits', {})[key] = dict(cleanup,
                    route='archived_release', marker=str(marker), owner=record['owner'],
                    archive_sha256=archived_shell_digest(data, key, ledger))
            else:
                released['marker_cleanup'] = cleanup
                _archive_shell_release(ledger, data, key, reader)
            write_ledger(ledger, data)
            return True
        if lines[0].isdecimal():
            if not record.get('leaf'):
                raise ValueError('The exact shell compiler leaf is not closed.')
            if not leaf_closed(reader, record['leaf']):
                raise LeafNotClosed('The exact shell compiler leaf is not closed.')
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
        if lines[0] == 'confirmed' and not require_dead_owner:
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
        if require_dead_owner and not ended_process(reader, record['owner']):
            raise ValueError('The shell reservation owner changed during release.')
        data['fixed_claims'][key] = 0
        data.setdefault('shell_releases', {})[key] = {'marker': str(marker), 'owner': record['owner'],
            'dead_owner_recovery': require_dead_owner,
            'previous_token_identity': record.get('token_identity'),
            'observed_token_identity': token_identity}
        _archive_shell_release(ledger, data, key, reader)
        prune_closed_aggregate_holds(data, reader)
        write_ledger(ledger, data)
        marker.unlink()
        return True
