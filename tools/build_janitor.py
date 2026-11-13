#!/usr/bin/env python3
"""Keep `_build/agents` and worktree build directories inside their disk budget.

The default is a dry run. It measures, writes `_build/BUDGET.json` and a plan,
and deletes nothing. `--apply` also deletes:

  * run dirs (`_build/agents/<agent>/<item>`) that are sealed (`SEALED.json`)
    or have no change for 24 h shrink to their non-compiled files under 1 MiB,
    plus the files that a `KEEP.json` names;
  * worktree `_build` dirs with no change for 48 h (the checkout stays);
  * banks of older main commits with no change for 24 h.

The janitor never touches `_build/agents/orch/`, a path that a live process
uses (cwd, executable, command line, environment, open or mapped files), a
path under which the admission ledger names a release receipt, a fresh
unsealed run, the bank of the newest main commit, or a run that one of
those names by a symbolic link or by a path in a manifest. It logs every
deletion under `_build/janitor/`.

Subcommands for other tools:
  admit                   exit 3 when this agent is over its budget (no scan)
  in-use PATH...          exit 0 when a live process uses one of the paths, or the
                          admission ledger names a release receipt under one
  branch-items BRANCH     list (or --delete) the run dirs tied to a branch
"""

import argparse
import array
import bisect
import contextlib
import errno
import fcntl
import gzip
import json
import os
from pathlib import Path
import re
import shutil
import stat
import struct
import subprocess
import sys
import time

GB = 10 ** 9
# The only place that sets the budgets. BUDGET.json and admission read them from here.
AGENT_BUDGET_BYTES = 80 * GB
TOTAL_BUDGET_BYTES = 200 * GB
RUN_IDLE_SECONDS = 24 * 3600
WORKTREE_IDLE_SECONDS = 48 * 3600
BANK_IDLE_SECONDS = 24 * 3600
SMALL_BYTES = 1 << 20
MANIFEST_MAX_BYTES = 256 << 20
PROTECTED_AGENTS = ('orch',)
COMPILED = ('.vo', '.vok', '.vos', '.glob', '.aux', '.cmi', '.cmo', '.cmx', '.cmxs', '.cma',
            '.cmxa', '.cmt', '.cmti', '.o', '.a', '.so', '.exe', '.bc', '.lia.cache',
            '.nia.cache', '.d', '.csexp', '.db', '-db')
MANIFEST = ('.json', '.jsonl', '.sh', '.py', '.install', '_CoqProject')
SEALED = ('SEALED.json', 'SEALED')
BANK_MANIFESTS = ('BANK.json', 'READY.json', 'COMPOSITION.json')
HEAD = re.compile(r'^[0-9a-f]{40}$')
NAME = rb'[^/\s"\'\\:,;)\]}]+'
REFERENCE = re.compile(rb'_build/agents/(' + NAME + rb')/(' + NAME + rb')|\.worktrees/('
                       + NAME + rb')/_build')
JANITOR_COMMAND = 'make janitor'

FS_IOC_FIEMAP = 0xC020660B
EXTENT_LAST, EXTENT_UNKNOWN, EXTENT_DELALLOC, EXTENT_SHARED = 0x1, 0x2, 0x4, 0x2000
FIEMAP_HEADER = struct.Struct('=QQIIII')
FIEMAP_EXTENT = struct.Struct('=QQQQQIIII')
FIEMAP_BATCH = 128


# --- measurement -------------------------------------------------------------

def extents(descriptor):
    """Yield (physical, length, flags) for every extent of an open file."""
    start = 0
    while True:
        buffer = bytearray(FIEMAP_HEADER.size + FIEMAP_BATCH * FIEMAP_EXTENT.size)
        FIEMAP_HEADER.pack_into(buffer, 0, start, (1 << 64) - 1 - start, 0, 0, FIEMAP_BATCH, 0)
        fcntl.ioctl(descriptor, FS_IOC_FIEMAP, buffer)
        mapped = FIEMAP_HEADER.unpack_from(buffer, 0)[3]
        last = mapped < FIEMAP_BATCH
        logical = length = 0
        for index in range(mapped):
            logical, physical, length, _, _, flags, _, _, _ = FIEMAP_EXTENT.unpack_from(
                buffer, FIEMAP_HEADER.size + index * FIEMAP_EXTENT.size)
            yield physical, length, flags
            last = last or bool(flags & EXTENT_LAST)
        if last:
            return
        start = logical + length


def compiled_or_large(name, size):
    return size >= SMALL_BYTES or name.endswith(COMPILED)


def survey(unit):
    """Walk one run dir (or a list of loose files) without following links.

    Return its newest change time, its shrinkable files, its symbolic link
    targets, its seal, KEEP.json and bank markers, and its extent usage:
    bytes in unshared extents plus the shared (or hard-linked) extents.
    """
    path, measure = unit['path'], unit.get('measure', True)
    result = {key: unit[key] for key in ('agent', 'item', 'worktree', 'head') if key in unit}
    result.update(path=path, newest=0.0, files=0, bytes=0, shrink_files=0, shrink_bytes=0,
                  unique=0, json_unshared=0, links=[], sealed=False, keep_files=[], banks=[],
                  errors=0)
    shared = {}
    pending = []
    for entry in unit.get('files') or [path]:
        try:
            info = os.lstat(entry)
        except OSError:
            result['errors'] += 1
            continue
        pending.append((entry, info, 0))
    if not unit.get('files') and pending and stat.S_ISDIR(pending[0][1].st_mode):
        names = set()
        with contextlib.suppress(OSError):
            names = set(os.listdir(path))
        result['sealed'] = any(name in names for name in SEALED)
    while pending:
        entry, info, depth = pending.pop()
        result['newest'] = max(result['newest'], info.st_mtime, info.st_ctime)
        mode = info.st_mode
        if stat.S_ISDIR(mode):
            try:
                children = list(os.scandir(entry))
            except OSError:
                result['errors'] += 1
                continue
            names = {child.name for child in children}
            if 'KEEP.json' in names:
                result['keep_files'].append(os.path.join(entry, 'KEEP.json'))
            if 'bank' in names and depth <= 2:
                head = bank_head(entry, names)
                if head:
                    result['banks'].append([entry, head])
            for child in children:
                try:
                    pending.append((child.path, child.stat(follow_symlinks=False), depth + 1))
                except OSError:
                    result['errors'] += 1
            continue
        if stat.S_ISLNK(mode):
            with contextlib.suppress(OSError):
                target = os.readlink(entry)
                result['links'].append(os.path.normpath(os.path.join(os.path.dirname(entry), target)))
            continue
        if not stat.S_ISREG(mode):
            continue
        result['files'] += 1
        result['bytes'] += info.st_size
        name = os.path.basename(entry)
        if compiled_or_large(name, info.st_size):
            result['shrink_files'] += 1
            result['shrink_bytes'] += info.st_size
        if measure and info.st_blocks:
            measure_file(entry, info, result, shared)
    if shared:
        starts = sorted(shared)
        result['shared'] = (array.array('q', starts).tobytes(),
                            array.array('q', (shared[start] for start in starts)).tobytes())
    return result


def measure_file(path, info, result, shared):
    allocated = info.st_blocks * 512
    try:
        descriptor = os.open(path, os.O_RDONLY | os.O_NOFOLLOW | os.O_NONBLOCK | os.O_CLOEXEC)
    except OSError:
        result['unique'] += allocated
        result['errors'] += 1
        return
    unshared = 0
    try:
        linked = info.st_nlink > 1
        for physical, length, flags in extents(descriptor):
            if flags & (EXTENT_UNKNOWN | EXTENT_DELALLOC):
                unshared += length
            elif linked or flags & EXTENT_SHARED:
                if length > shared.get(physical, 0):
                    shared[physical] = length
            else:
                unshared += length
    except OSError:
        unshared = allocated
        result['errors'] += 1
    finally:
        os.close(descriptor)
    result['unique'] += unshared
    if path.endswith('.json') and info.st_size >= SMALL_BYTES:
        result['json_unshared'] += unshared


def bank_head(directory, names):
    for name in BANK_MANIFESTS:
        if name in names:
            try:
                with open(os.path.join(directory, name), 'rb') as stream:
                    if os.fstat(stream.fileno()).st_size > MANIFEST_MAX_BYTES:
                        continue
                    value = json.load(stream)
            except (OSError, ValueError):
                continue
            head = value.get('head') if isinstance(value, dict) else None
            if isinstance(head, str) and HEAD.match(head):
                return head
    return None


def merge_shared(target, result):
    """Add one survey's shared extents to a {physical: length} map."""
    if 'shared' not in result:
        return
    starts, lengths = array.array('q'), array.array('q')
    starts.frombytes(result['shared'][0])
    lengths.frombytes(result['shared'][1])
    for start, length in zip(starts, lengths):
        if length > target.get(start, 0):
            target[start] = length


def union_bytes(shared):
    total, end = 0, -1
    for start in sorted(shared):
        stop = start + shared[start]
        if stop > end:
            total += stop - max(start, end)
            end = stop
    return total


def references(path):
    """Return the run dirs and worktree builds that manifests in PATH name."""
    items, worktrees = set(), set()
    for directory, subdirectories, files in os.walk(path):
        for name in files:
            if not name.endswith(MANIFEST):
                continue
            file = os.path.join(directory, name)
            try:
                if os.lstat(file).st_size > MANIFEST_MAX_BYTES or os.path.islink(file):
                    continue
                with open(file, 'rb') as stream:
                    data = stream.read()
            except OSError:
                continue
            for match in REFERENCE.finditer(data):
                if match.group(1):
                    items.add((match.group(1).decode(errors='replace'),
                               match.group(2).decode(errors='replace')))
                else:
                    worktrees.add(match.group(3).decode(errors='replace'))
    return {'path': path, 'items': sorted(items), 'worktrees': sorted(worktrees)}


def parallel(function, units, jobs):
    if jobs <= 1 or len(units) <= 1:
        return [function(unit) for unit in units]
    import multiprocessing
    with multiprocessing.get_context('fork').Pool(jobs) as pool:
        return list(pool.imap(function, units, chunksize=1))


# --- live processes ------------------------------------------------------------

class LivePaths:
    """Paths that live processes use, normalized and sorted for prefix search."""

    def __init__(self, paths, owners):
        self.paths = sorted(paths)
        self.owners = owners

    @classmethod
    def scan(cls, root, proc='/proc', exclude=()):
        root = os.path.realpath(root)
        found, owners = set(), {}
        exclude = {str(pid) for pid in exclude}
        try:
            pids = [name for name in os.listdir(proc) if name.isdigit() and name not in exclude]
        except OSError:
            pids = []
        for pid in pids:
            base = os.path.join(proc, pid)
            for path in process_paths(base):
                if path == root or path.startswith(root + '/'):
                    # A command line can name a run through a symbolic link.
                    path = os.path.realpath(path)
                    found.add(path)
                    owners.setdefault(path, pid)
        return cls(found, owners)

    def user(self, path):
        """Return a live path inside PATH (or PATH itself), else None."""
        path = os.path.realpath(path)
        index = bisect.bisect_left(self.paths, path)
        if index < len(self.paths) and self.paths[index] == path:
            return path
        index = bisect.bisect_left(self.paths, path + '/')
        if index < len(self.paths) and self.paths[index].startswith(path + '/'):
            return self.paths[index]
        return None


def process_paths(base):
    paths = []
    cwd = None
    for name in ('cwd', 'exe', 'root'):
        with contextlib.suppress(OSError):
            value = os.readlink(os.path.join(base, name))
            paths.append(value)
            if name == 'cwd':
                cwd = value
    with contextlib.suppress(OSError):
        for descriptor in os.listdir(os.path.join(base, 'fd')):
            with contextlib.suppress(OSError):
                paths.append(os.readlink(os.path.join(base, 'fd', descriptor)))
    with contextlib.suppress(OSError):
        with open(os.path.join(base, 'maps'), 'rb') as stream:
            for line in stream:
                fields = line.split(None, 5)
                if len(fields) == 6 and fields[5].startswith(b'/'):
                    paths.append(fields[5].strip().decode(errors='replace'))
    for name in ('cmdline', 'environ'):
        with contextlib.suppress(OSError):
            with open(os.path.join(base, name), 'rb') as stream:
                data = stream.read()
            for token in re.split(rb'[\0=:,\s]+', data):
                if b'/' not in token:
                    continue
                token = token.decode(errors='replace')
                if not token.startswith('/'):
                    if cwd is None:
                        continue
                    token = os.path.join(cwd, token)
                paths.append(token)
    result = []
    for path in paths:
        if path.endswith(' (deleted)'):
            path = path[:-len(' (deleted)')]
        if path.startswith('/'):
            result.append(os.path.normpath(path))
    return result


# --- admission ledger ----------------------------------------------------------

LEDGER = Path('_build/agents/worker-build-2/native-region-release-v1/LEDGER.json')


def ledger_receipts(root):
    """Return the release receipts the admission ledger reads on every admission.

    On 2026-11-12 a worktree removal deleted the 6ae0 release receipt, and every
    admission crashed until the entry was dropped from the ledger.
    """
    path = Path(os.environ.get('ZESU_CANONICAL_LEDGER', Path(root) / LEDGER))
    try:
        data = json.loads(path.read_text())
    except FileNotFoundError:
        return []
    receipts = []
    for release in data.get('released_region_claims', {}).values():
        for name in ('receipt', 'stop_receipt'):
            if isinstance(release.get(name), str):
                receipts.append(release[name])
    return receipts


def receipts_under(receipts, path):
    prefix = os.path.realpath(path).rstrip(os.sep) + os.sep
    return [receipt for receipt in receipts if os.path.realpath(receipt).startswith(prefix)]


# --- repository and git --------------------------------------------------------

def base_root(start=None):
    """Return the base checkout that owns the Git common directory."""
    start = Path(start or Path(__file__).resolve().parent)
    try:
        common = subprocess.run(['git', '-C', str(start), 'rev-parse', '--path-format=absolute',
                                 '--git-common-dir'], check=True, capture_output=True,
                                text=True).stdout.strip()
        return Path(common).parent
    except (OSError, subprocess.CalledProcessError):
        return start.parent


def git(root, *arguments):
    return subprocess.run(['git', '-C', str(root), *arguments], capture_output=True, text=True)


def commit(root, ref):
    result = git(root, 'rev-parse', '--verify', '-q', ref + '^{commit}')
    return result.stdout.strip() if result.returncode == 0 else None


def is_ancestor(root, older, newer):
    return git(root, 'merge-base', '--is-ancestor', older, newer).returncode == 0


def locked_worktrees(root):
    result = git(root, 'worktree', 'list', '--porcelain')
    locked, current = set(), None
    for line in result.stdout.splitlines() if result.returncode == 0 else []:
        if line.startswith('worktree '):
            current = os.path.realpath(line[len('worktree '):])
        elif line.startswith('locked') and current:
            locked.add(current)
    return locked


# --- plan ----------------------------------------------------------------------

class Janitor:
    def __init__(self, root, *, now=None, jobs=8, proc='/proc', main_ref='origin/main',
                 agent_budget=AGENT_BUDGET_BYTES, total_budget=TOTAL_BUDGET_BYTES,
                 protected_agents=PROTECTED_AGENTS, log_dir=None):
        self.root = Path(root).resolve()
        self.build = self.root / '_build'
        self.agents = self.build / 'agents'
        self.now = time.time() if now is None else now
        self.jobs = jobs
        self.proc = proc
        self.main_ref = main_ref
        self.agent_budget = agent_budget
        self.total_budget = total_budget
        self.protected_agents = set(protected_agents)
        self.log_dir = Path(log_dir) if log_dir else self.build / 'janitor'
        self.stamp = time.strftime('%Y%m%dT%H%M%SZ', time.gmtime(self.now))

    # Units ------------------------------------------------------------------

    def run_units(self, agents=None):
        units = []
        if not self.agents.is_dir():
            return units
        for agent in sorted(os.listdir(self.agents)):
            directory = self.agents / agent
            if (agents is not None and agent not in agents) or directory.is_symlink() \
                    or not directory.is_dir():
                continue
            loose = []
            for item in sorted(os.listdir(directory)):
                path = directory / item
                if path.is_dir() and not path.is_symlink():
                    units.append({'agent': agent, 'item': item, 'path': str(path)})
                else:
                    loose.append(str(path))
            if loose:
                units.append({'agent': agent, 'item': None, 'path': str(directory),
                              'files': loose})
        return units

    def worktree_builds(self):
        worktrees = self.root / '.worktrees'
        if not worktrees.is_dir():
            return []
        found = []
        for name in sorted(os.listdir(worktrees)):
            build = worktrees / name / '_build'
            if build.is_dir() and not build.is_symlink():
                found.append({'worktree': name, 'path': str(build), 'measure': False})
        return found

    def bank_dirs(self):
        banks = self.build / 'banks'
        if not banks.is_dir():
            return []
        found = []
        for name in sorted(os.listdir(banks)):
            path = banks / name
            if path.is_dir() and not path.is_symlink():
                names = set(os.listdir(path))
                head = name if HEAD.match(name) else bank_head(str(path), names)
                found.append({'head': head, 'path': str(path), 'measure': False})
        return found

    # Survey -----------------------------------------------------------------

    def survey_runs(self, agents=None):
        return parallel(survey, self.run_units(agents), self.jobs)

    def budget(self, runs):
        """Unique bytes per agent and in total, as `gdu --reflink` counts them."""
        by_agent, total_shared, total_unique, report = {}, {}, 0, {}
        for result in runs:
            by_agent.setdefault(result['agent'], []).append(result)
        for agent, results in sorted(by_agent.items()):
            shared = {}
            for result in results:
                merge_shared(shared, result)
            unshared = sum(result['unique'] for result in results)
            unique = unshared + union_bytes(shared)
            total_unique += unshared
            for start, length in shared.items():
                if length > total_shared.get(start, 0):
                    total_shared[start] = length
            del shared
            report[agent] = {'unique_bytes': unique, 'budget_bytes': self.agent_budget,
                             'over': unique > self.agent_budget,
                             'protected': agent in self.protected_agents,
                             'unshared_large_json_bytes': sum(r['json_unshared'] for r in results)}
        total = total_unique + union_bytes(total_shared)
        return {'schema': 'zesu.build-budget.v1',
                'measured_at': time.strftime('%Y-%m-%dT%H:%M:%SZ', time.gmtime(self.now)),
                'root': str(self.agents),
                'agent_budget_bytes': self.agent_budget,
                'total_budget_bytes': self.total_budget,
                'total_unique_bytes': total,
                'total_over': total > self.total_budget,
                'janitor': JANITOR_COMMAND,
                'agents': report}

    # Plan -------------------------------------------------------------------

    def plan(self, runs, live):
        """Decide one action per run dir, worktree build, and bank."""
        items = {(r['agent'], r['item']): r for r in runs if r['item'] is not None}
        reasons = {}

        def protect(key, reason):
            if key in items and key not in reasons:
                reasons[key] = reason
                return True
            return False

        main = commit(self.root, self.main_ref)
        receipts = ledger_receipts(self.root)
        banks = []
        for key, result in items.items():
            for bank_root, head in result['banks']:
                banks.append({'key': key, 'path': os.path.join(bank_root, 'bank'), 'head': head,
                              'newest': result['newest']})
        bank_units = self.bank_dirs()
        build_banks = [dict(unit, newest=result['newest'], key=None)
                       for unit, result in zip(bank_units, parallel(survey, bank_units, self.jobs))]
        newest_heads, older_heads = self.main_bank_heads(main, banks + build_banks)

        for key, result in items.items():
            agent, item = key
            if agent in self.protected_agents:
                protect(key, 'protected agent')
            elif live.user(result['path']):
                protect(key, 'live process uses ' + live.user(result['path']))
            elif receipts_under(receipts, result['path']):
                protect(key, 'admission ledger receipt ' + receipts_under(receipts, result['path'])[0])
            elif self.now - result['newest'] < RUN_IDLE_SECONDS and not result['sealed']:
                protect(key, 'changed in the last 24 h')
            elif any(head in newest_heads for _, head in result['banks']):
                protect(key, 'bank of the newest main commit')
        for link in self.top_level_links():
            key = self.item_key(link)
            if key:
                protect(key, 'target of ' + os.path.relpath(link['from'], self.root))

        roots = [items[key]['path'] for key in reasons]
        referenced_worktrees = set()
        for found in parallel(references, roots, self.jobs):
            owner = self.item_key({'to': found['path']})
            for key in found['items']:
                protect(tuple(key), 'named by a manifest in ' + '/'.join(owner or ('?',)))
            referenced_worktrees.update(found['worktrees'])
        pending = list(reasons)
        while pending:
            key = pending.pop()
            for target in items[key]['links']:
                other = self.item_key({'to': target})
                if other and protect(other, 'symbolic link target of ' + '/'.join(key)):
                    pending.append(other)
                worktree = self.worktree_of(target)
                if worktree:
                    referenced_worktrees.add(worktree)

        rows = []
        for key, result in sorted(items.items()):
            row = {'kind': 'run', 'path': result['path'], 'check': result['path'],
                   'agent': key[0], 'bytes': result['bytes'], 'files': result['files']}
            if key in reasons:
                row.update(action='keep', reason=reasons[key])
            elif result['keep_files'] and keep_paths(result) is None:
                row.update(action='keep', reason='unreadable KEEP.json')
            else:
                shrink_files, shrink_bytes = result['shrink_files'], result['shrink_bytes']
                if result['keep_files']:
                    shrink_files, shrink_bytes = shrink_totals(result)
                row.update(action='shrink' if shrink_files else 'keep',
                           reason='sealed' if result['sealed'] else 'no change for 24 h',
                           delete_files=shrink_files, delete_bytes=shrink_bytes,
                           newest=result['newest'])
                if not shrink_files:
                    row['reason'] = 'already small'
            rows.append(row)

        for bank in banks + build_banks:
            key = bank['key']
            row = {'kind': 'bank', 'path': bank['path'], 'head': bank['head'],
                   'check': items[key]['path'] if key else bank['path']}
            if bank['head'] not in older_heads:
                continue
            if key in reasons:
                row.update(action='keep', reason=reasons[key])
            elif live.user(row['check']):
                row.update(action='keep', reason='live process uses ' + live.user(row['check']))
            elif self.now - bank['newest'] < BANK_IDLE_SECONDS:
                row.update(action='keep', reason='changed in the last 24 h')
            else:
                row.update(action='delete', reason='bank of an older main commit',
                           newest=bank['newest'])
            rows.append(row)

        locked = locked_worktrees(self.root)
        worktree_units = self.worktree_builds()
        for unit, result in zip(worktree_units, parallel(survey, worktree_units, self.jobs)):
            checkout = os.path.dirname(unit['path'])
            row = {'kind': 'worktree-build', 'path': unit['path'], 'check': checkout,
                   'bytes': result['bytes'], 'files': result['files']}
            user = live.user(checkout)
            if user:
                row.update(action='keep', reason='live process uses ' + user)
            elif os.path.realpath(checkout) in locked:
                row.update(action='keep', reason='worktree is locked')
            elif receipts_under(receipts, unit['path']):
                row.update(action='keep', reason='admission ledger receipt '
                           + receipts_under(receipts, unit['path'])[0])
            elif unit['worktree'] in referenced_worktrees:
                row.update(action='keep', reason='named by a kept run')
            elif self.now - result['newest'] < WORKTREE_IDLE_SECONDS:
                row.update(action='keep', reason='changed in the last 48 h')
            else:
                row.update(action='delete', reason='no change for 48 h',
                           newest=result['newest'])
            rows.append(row)
        return {'main': main, 'rows': rows}

    def main_bank_heads(self, main, banks):
        """Split bank heads on main into the newest heads and older heads."""
        if not main:
            return set(), set()
        heads = {bank['head'] for bank in banks if bank['head']}
        on_main = {head for head in heads if head == main or is_ancestor(self.root, head, main)}
        newest = {head for head in on_main
                  if not any(other != head and is_ancestor(self.root, head, other)
                             for other in on_main)}
        return newest, on_main - newest

    def top_level_links(self):
        links = []
        if self.build.is_dir():
            for name in os.listdir(self.build):
                path = self.build / name
                if path.is_symlink():
                    links.append({'from': str(path),
                                  'to': os.path.normpath(os.path.join(self.build,
                                                                      os.readlink(path)))})
        return links

    def item_key(self, link):
        try:
            parts = Path(link['to']).relative_to(self.agents).parts
        except ValueError:
            return None
        return (parts[0], parts[1]) if len(parts) >= 2 else None

    def worktree_of(self, target):
        try:
            parts = Path(target).relative_to(self.root / '.worktrees').parts
        except ValueError:
            return None
        return parts[0] if len(parts) >= 2 and parts[1] == '_build' else None

    # Apply ------------------------------------------------------------------

    def apply(self, plan, live, log):
        """Delete what the plan names. Check every target before the first deletion."""
        freed = {'files': 0, 'bytes': 0}
        touched = set()
        targets = []
        for row in plan['rows']:
            if row.get('action') not in ('shrink', 'delete'):
                continue
            user = live.user(row['check'])
            if user:
                row.update(action='keep', reason='live process uses ' + user)
            elif newest_top(row['path']) > row['newest']:
                row.update(action='keep', reason='changed during the janitor run')
            else:
                targets.append(row)
        targets.sort(key=lambda row: row['kind'] == 'run')
        for row in targets:
            if row['kind'] == 'run':
                files, size = shrink(row['path'], log)
                touched.add(row['agent'])
            else:
                files, size = remove_tree(row['path'], log)
                agent = self.item_key({'to': row['path']})
                if agent:
                    touched.add(agent[0])
            row.update(deleted_files=files, deleted_bytes=size)
            freed['files'] += files
            freed['bytes'] += size
        return freed, touched

    def write_json(self, path, value):
        path.parent.mkdir(parents=True, exist_ok=True)
        temporary = path.with_name('.' + path.name + '.tmp')
        temporary.write_text(json.dumps(value, indent=2, sort_keys=True) + '\n')
        os.replace(temporary, path)


def newest_top(path):
    try:
        info = os.lstat(path)
    except OSError:
        return float('inf')
    return max(info.st_mtime, info.st_ctime)


def keep_paths(result):
    """Read KEEP.json files. A file is a list of paths, or {"keep": [...]}."""
    kept = []
    for keep in result['keep_files']:
        base = os.path.dirname(keep)
        try:
            value = json.loads(Path(keep).read_text())
        except (OSError, ValueError):
            return None
        entries = value.get('keep') if isinstance(value, dict) else value
        if not isinstance(entries, list) or not all(isinstance(x, str) for x in entries):
            return None
        kept.append(keep)
        kept.extend(os.path.normpath(os.path.join(base, entry)) for entry in entries)
    return kept


def is_kept(path, kept):
    return any(path == entry or path.startswith(entry + '/') for entry in kept)


def shrink_candidates(result):
    kept = keep_paths(result) if result['keep_files'] else []
    if kept is None:
        return
    for directory, subdirectories, files in os.walk(result['path']):
        for name in files:
            path = os.path.join(directory, name)
            try:
                info = os.lstat(path)
            except OSError:
                continue
            if stat.S_ISREG(info.st_mode) and compiled_or_large(name, info.st_size) \
                    and not is_kept(path, kept):
                yield path, info.st_size


def shrink_totals(result):
    files = size = 0
    for _, length in shrink_candidates(result):
        files += 1
        size += length
    return files, size


def unlink(path):
    try:
        os.unlink(path)
    except PermissionError:
        parent = os.path.dirname(path)
        mode = os.stat(parent).st_mode
        os.chmod(parent, mode | stat.S_IWUSR | stat.S_IXUSR)
        try:
            os.unlink(path)
        finally:
            os.chmod(parent, stat.S_IMODE(mode))


def shrink(path, log):
    keep = []
    for directory, subdirectories, files in os.walk(path):
        if 'KEEP.json' in files:
            keep.append(os.path.join(directory, 'KEEP.json'))
    files = size = 0
    for file, length in shrink_candidates({'path': path, 'keep_files': keep}):
        try:
            unlink(file)
        except OSError as error:
            log.write(f'{time.time():.0f}\tfailed\t{file}\t{length}\t{error}\n')
            continue
        log.write(f'{time.time():.0f}\tshrink\t{file}\t{length}\n')
        files += 1
        size += length
    return files, size


def remove_tree(path, log):
    files = size = 0
    for directory, subdirectories, names in os.walk(path):
        for name in names:
            with contextlib.suppress(OSError):
                info = os.lstat(os.path.join(directory, name))
                files += 1
                size += info.st_size if stat.S_ISREG(info.st_mode) else 0

    def writable(function, failed, error):
        parent = os.path.dirname(failed)
        with contextlib.suppress(OSError):
            os.chmod(parent, os.stat(parent).st_mode | stat.S_IWUSR | stat.S_IXUSR)
        function(failed)

    shutil.rmtree(path, onexc=writable)
    log.write(f'{time.time():.0f}\tremove-tree\t{path}\t{size}\tfiles={files}\n')
    return files, size


# --- commands ------------------------------------------------------------------

def human(size):
    return f'{size / GB:.1f} GB'


@contextlib.contextmanager
def exclusive(log_dir):
    log_dir.mkdir(parents=True, exist_ok=True)
    with open(log_dir / '.lock', 'w') as lock:
        try:
            fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
        except OSError as error:
            if error.errno in (errno.EAGAIN, errno.EACCES):
                raise SystemExit('build janitor: another janitor holds ' + str(log_dir / '.lock'))
            raise
        yield


def run(args):
    janitor = Janitor(args.root or base_root(), jobs=args.jobs, main_ref=args.main_ref,
                      agent_budget=int(args.agent_budget_gb * GB),
                      total_budget=int(args.total_budget_gb * GB), log_dir=args.log_dir)
    mode = 'apply' if args.apply else 'dry-run'
    with exclusive(janitor.log_dir):
        exclude = {os.getpid(), os.getppid()}
        runs = janitor.survey_runs()
        live = LivePaths.scan(janitor.root, janitor.proc, exclude)
        plan = janitor.plan(runs, live)
        budget = janitor.budget(runs)
        freed = None
        if args.apply:
            live = LivePaths.scan(janitor.root, janitor.proc, exclude)
            deleted = janitor.log_dir / f'deleted-{janitor.stamp}.tsv.gz'
            with gzip.open(deleted, 'wt') as log:
                freed, touched = janitor.apply(plan, live, log)
            if touched:
                again = janitor.survey_runs(touched)
                runs = [r for r in runs if r['agent'] not in touched] + again
                budget = janitor.budget(runs)
        janitor.write_json(Path(args.budget) if args.budget else janitor.build / 'BUDGET.json',
                           budget)
        janitor.write_json(janitor.log_dir / f'plan-{janitor.stamp}-{mode}.json',
                           {'mode': mode, 'root': str(janitor.root), 'main': plan['main'],
                            'freed': freed, 'rows': plan['rows']})
        lines = summary(plan, budget, mode, freed)
        with open(janitor.log_dir / 'janitor.log', 'a') as log:
            for line in lines:
                log.write(f'{janitor.stamp}\t{mode}\t{line}\n')
        print('\n'.join(lines))
        print('plan: ' + str(janitor.log_dir / f'plan-{janitor.stamp}-{mode}.json'))
    return 0


def summary(plan, budget, mode, freed):
    lines = [f'build janitor ({mode}): total {human(budget["total_unique_bytes"])} of '
             f'{human(budget["total_budget_bytes"])}'
             + (' (OVER BUDGET)' if budget['total_over'] else '')]
    for agent, row in budget['agents'].items():
        if row['over']:
            lines.append(f'over budget: {agent} {human(row["unique_bytes"])} of '
                         f'{human(row["budget_bytes"])}'
                         + (' (protected, never refused)' if row['protected'] else ''))
    totals = {}
    for row in plan['rows']:
        key = (row['kind'], row.get('action'))
        count, size = totals.get(key, (0, 0))
        totals[key] = (count + 1, size + row.get('delete_bytes', row.get('bytes', 0)))
    for (kind, action), (count, size) in sorted(totals.items(), key=lambda x: str(x[0])):
        lines.append(f'{kind} {action}: {count} ({human(size)} apparent)')
    if freed is not None:
        lines.append(f'deleted {freed["files"]} files, {human(freed["bytes"])} apparent')
    return lines


def agent_of(environment, build):
    """Name the agent whose `_build/agents/<agent>` a new run writes."""
    if environment.get('ZESU_BUILD_AGENT'):
        return environment['ZESU_BUILD_AGENT']
    directory = environment.get('AGENT_BUILD_DIR')
    if directory:
        try:
            parts = Path(directory).resolve().relative_to((build / 'agents').resolve()).parts
            if parts:
                return parts[0]
        except (OSError, ValueError):
            pass
    return environment.get('COORD_AGENT') or None


def admit(args, environment=os.environ):
    """Refuse a new run for an agent over its budget. Read only the budget file."""
    path = Path(environment.get('ZESU_BUILD_BUDGET') or
                (Path(args.root) if args.root else base_root()) / '_build/BUDGET.json')
    try:
        budget = json.loads(path.read_text())
        rows = budget['agents']
    except FileNotFoundError:
        return 0
    except (OSError, ValueError, KeyError, TypeError) as error:
        print(f'build budget: ignoring unreadable {path}: {error}', file=sys.stderr)
        return 0
    agent = agent_of(environment, path.parent)
    row = rows.get(agent) if agent else None
    if not isinstance(row, dict) or not row.get('over') or row.get('protected'):
        return 0
    print(f'resource guard: refused: agent {agent} uses {human(row["unique_bytes"])} of its '
          f'{human(row["budget_bytes"])} build budget under _build/agents/{agent} '
          f'({path}, measured {budget.get("measured_at", "?")}).\n'
          f'Run `{JANITOR_COMMAND}` to see what the janitor frees, `{JANITOR_COMMAND}-apply` '
          f'to free it, or delete your own finished run dirs. Each janitor run refreshes '
          f'the budget.', file=sys.stderr)
    return 3


def in_use(args):
    root = Path(args.root) if args.root else base_root()
    live = LivePaths.scan(root, exclude={os.getpid(), os.getppid()})
    receipts = ledger_receipts(root)
    status = 1
    for path in args.paths:
        user = live.user(path)
        if user:
            print(f'{path}: live process {live.owners.get(user, "?")} uses {user}')
            status = 0
        for receipt in receipts_under(receipts, path):
            print(f'{path}: the admission ledger names receipt {receipt}')
            status = 0
    return status


def branch_items(args):
    """List or delete the `_build/agents/*/<item>` dirs that belong to BRANCH."""
    root = Path(args.root) if args.root else base_root()
    janitor = Janitor(root, log_dir=args.log_dir)
    names = {args.branch, args.branch.replace('/', '-'), args.branch.rsplit('/', 1)[-1]}
    live = LivePaths.scan(root, exclude={os.getpid(), os.getppid()})
    receipts = ledger_receipts(root)
    rows = []
    for unit in janitor.run_units():
        if unit['item'] is None:
            continue
        owner = None
        with contextlib.suppress(OSError, ValueError, AttributeError):
            owner = json.loads((Path(unit['path']) / 'ITEM.json').read_text()).get('branch')
        if owner != args.branch and not (owner is None and unit['item'] in names):
            continue
        if unit['agent'] in janitor.protected_agents:
            rows.append((unit['path'], 'kept: protected agent'))
        elif live.user(unit['path']):
            rows.append((unit['path'], 'kept: live process uses ' + live.user(unit['path'])))
        elif receipts_under(receipts, unit['path']):
            rows.append((unit['path'], 'kept: admission ledger receipt '
                         + receipts_under(receipts, unit['path'])[0]))
        else:
            rows.append((unit['path'], None))
    if not rows:
        print(f'no run dirs under {janitor.agents} belong to {args.branch}')
        return 0
    with contextlib.ExitStack() as stack:
        log = None
        if args.delete:
            stack.enter_context(exclusive(janitor.log_dir))
            log = stack.enter_context(gzip.open(
                janitor.log_dir / f'deleted-{janitor.stamp}-merge.tsv.gz', 'at'))
        for path, kept in rows:
            if kept:
                print(f'{kept}: {path}')
            elif args.delete:
                files, size = remove_tree(path, log)
                with open(janitor.log_dir / 'janitor.log', 'a') as summary_log:
                    summary_log.write(f'{janitor.stamp}\tmerge\tremoved {path} '
                                      f'({files} files, {human(size)}) for {args.branch}\n')
                print(f'removed run dir {path} ({files} files, {human(size)} apparent)')
            else:
                print(f'would remove run dir {path}')
    return 0


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__,
                                     formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument('--root', help='base checkout (default: owner of the Git common dir)')
    parser.add_argument('--log-dir', help='log and plan directory (default: _build/janitor)')
    parser.add_argument('--budget', help='budget file to write (default: _build/BUDGET.json)')
    sub = parser.add_subparsers(dest='command')
    parser.add_argument('--apply', action='store_true', help='delete; the default is a dry run')
    parser.add_argument('--dry-run', action='store_true', help='report only (the default)')
    parser.add_argument('--jobs', type=int, default=8)
    parser.add_argument('--main-ref', default='origin/main')
    parser.add_argument('--agent-budget-gb', type=float, default=AGENT_BUDGET_BYTES / GB,
                        help='budget for each agent (default: %(default)s GB)')
    parser.add_argument('--total-budget-gb', type=float, default=TOTAL_BUDGET_BYTES / GB,
                        help='budget for all agents together (default: %(default)s GB)')
    sub.add_parser('admit', help='exit 3 when this agent is over its budget')
    use = sub.add_parser('in-use', help='exit 0 when a live process uses a path')
    use.add_argument('paths', nargs='+')
    branch = sub.add_parser('branch-items', help='run dirs that belong to a merged branch')
    branch.add_argument('branch')
    branch.add_argument('--delete', action='store_true')
    args = parser.parse_args(argv)
    if args.apply and args.dry_run:
        parser.error('--apply and --dry-run exclude each other')
    if args.command == 'admit':
        return admit(args)
    if args.command == 'in-use':
        return in_use(args)
    if args.command == 'branch-items':
        return branch_items(args)
    return run(args)


if __name__ == '__main__':
    sys.exit(main())
