#!/usr/bin/env python3
"""Keep `_build/agents` and worktree build directories inside their disk budget.

The default is a dry run. It measures, writes `_build/BUDGET.json` and a plan,
and deletes nothing. `--apply` also deletes:

  * run dirs (`_build/agents/<agent>/<item>`) that are sealed (`SEALED.json`)
    or have no change for 24 h shrink to their non-compiled files under 1 MiB,
    plus the files that a `KEEP.json` names;
  * worktree `_build` dirs with no change for 48 h (the checkout stays);
  * banks of older main commits with no change for 24 h;
  * whole worktrees under `.worktrees/` (`git worktree remove`, never --force) that are
    clean (no tracked change), not in use (live process, admission receipt, or live
    registered run naming a path in them), unchanged for 6 h, and whose head is in
    origin/main, on a measurement branch (bench/*, orch/heldout-*; the branch stays) or
    a detached head that a branch or remote ref holds. A checkout idle over 7 days goes
    losslessly whatever its head: its unmerged branch is pushed to origin (no force), a
    detached head on no ref and any uncommitted work (tracked changes, untracked non-ignored
    files) go to a pushed `rescue/<name>-<date>` branch (`_build/janitor/rescued-worktrees.tsv`).
    Each removal goes to `_build/janitor/worktrees.log`. The run watchdog does the same when
    free disk is under 50 GB (reap_when_low).

The janitor never touches `_build/agents/orch/`, a path that a live process
uses (cwd, executable, command line, environment, open or mapped files), a
path under which the admission ledger names a release receipt, a fresh
unsealed run, the bank of the newest main commit, or a run that one of
those names by a symbolic link or by a path in a manifest. It logs every
deletion under `_build/janitor/`.

It never touches the saved-goal store `_build/goals/` (see goal_store.py) or the
closure-record store `_build/closures/`, and reports the goal store's size against its
budget. Before it deletes a worktree build or a merged branch's run dir, it moves the
saved goals and the CLOSURE.json / NOT-CLOSED.json records in it into those stores.

It also reports the per-user harness caches under ~/.cache/zesislar (size and
file count per directory) against CACHE_BUDGET_BYTES. Those caches bound
themselves; `tools/prune_caches.py` prunes them on demand.

Subcommands for other tools:
  admit                   exit 3 when this agent is over its budget (no scan)
  in-use PATH...          exit 0 when a live process uses one of the paths, or the
                          admission ledger names a release receipt under one
  branch-items BRANCH     list (or --delete) the run dirs tied to a branch
  rescue-goals PATH...    move the saved goals under each PATH into the store
  worktrees [--json F]    report every worktree's verdict (global --apply removes)
  remove-worktree [--wait] PATH...
                          a creator's end-of-run removal (bench.py, gate and
                          closed-set scripts): rescue goals, then git worktree remove
"""

from concurrent.futures import ThreadPoolExecutor
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

import goal_store

GB = 10 ** 9
# The only place that sets the budgets. BUDGET.json and admission read them from here.
AGENT_BUDGET_BYTES = 80 * GB
TOTAL_BUDGET_BYTES = 200 * GB
CACHE_BUDGET_BYTES = 5 * GB
CACHE_ROOT = Path.home() / '.cache/zesislar'
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


def cache_usage(root):
    """Allocated bytes and file counts of each directory under the per-user cache root."""
    dirs, total = {}, 0
    try:
        names = sorted(os.listdir(root))
    except OSError:
        names = []
    for name in names:
        size = files = 0
        for current, _, entries in os.walk(os.path.join(root, name)):
            for entry in entries:
                with contextlib.suppress(OSError):
                    size += os.lstat(os.path.join(current, entry)).st_blocks * 512
                    files += 1
        with contextlib.suppress(OSError):
            # The directory's own blocks: a flat store with millions of entries keeps
            # a large directory file even after they are deleted.
            size += os.lstat(os.path.join(root, name)).st_blocks * 512
        dirs[name] = {'bytes': size, 'files': files}
        total += size
    return {'bytes': total, 'dirs': dirs}


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
                 protected_agents=PROTECTED_AGENTS, log_dir=None, cache_root=None):
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
        self.cache_root = Path(CACHE_ROOT if cache_root is None else cache_root)

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
        goals = goal_store.store_bytes(self.root)
        caches = cache_usage(self.cache_root)
        return {'schema': 'zesu.build-budget.v1',
                'measured_at': time.strftime('%Y-%m-%dT%H:%M:%SZ', time.gmtime(self.now)),
                'root': str(self.agents),
                'agent_budget_bytes': self.agent_budget,
                'total_budget_bytes': self.total_budget,
                'total_unique_bytes': total,
                'total_over': total > self.total_budget,
                'janitor': JANITOR_COMMAND,
                'goal_store': {'path': str(self.root / goal_store.STORE), 'bytes': goals,
                               'budget_bytes': goal_store.GOAL_STORE_BUDGET_BYTES,
                               'over': goals > goal_store.GOAL_STORE_BUDGET_BYTES},
                'caches': {'path': str(self.cache_root), 'bytes': caches['bytes'],
                           'budget_bytes': CACHE_BUDGET_BYTES,
                           'over': caches['bytes'] > CACHE_BUDGET_BYTES,
                           'prune': 'tools/prune_caches.py', 'dirs': caches['dirs']},
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
        """Delete what the plan names. Check every target before the first deletion.

        A deletion that fails (ENOTEMPTY, EBUSY, a path in use) is logged, recorded on its
        row, and skipped; the run continues. Return (freed, touched, failures).
        """
        freed = {'files': 0, 'bytes': 0}
        touched = set()
        failures = 0
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
            try:
                if row['kind'] == 'run':
                    files, size, failed = shrink(row['path'], log)
                    touched.add(row['agent'])
                else:
                    rescue_goals(self.root, row['path'], 'build janitor: ' + row['reason'], log)
                    files, size, failed = remove_tree(row['path'], log)
                    agent = self.item_key({'to': row['path']})
                    if agent:
                        touched.add(agent[0])
            except OSError as error:
                log.write(f'{time.time():.0f}\tfailed\t{row["path"]}\t0\t{error}\n')
                print(f'build janitor: skipped {row["path"]}: {error}', file=sys.stderr)
                files, size, failed = 0, 0, 1
            row.update(deleted_files=files, deleted_bytes=size)
            if failed:
                row['failed'] = failed
                failures += 1
            freed['files'] += files
            freed['bytes'] += size
        return freed, touched, failures

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
    files = size = failed = 0
    for file, length in shrink_candidates({'path': path, 'keep_files': keep}):
        try:
            unlink(file)
        except OSError as error:
            log.write(f'{time.time():.0f}\tfailed\t{file}\t{length}\t{error}\n')
            failed += 1
            continue
        log.write(f'{time.time():.0f}\tshrink\t{file}\t{length}\n')
        files += 1
        size += length
    return files, size, failed


def tree_totals(path):
    files = size = 0
    for directory, subdirectories, names in os.walk(path):
        for name in names:
            with contextlib.suppress(OSError):
                info = os.lstat(os.path.join(directory, name))
                files += 1
                size += info.st_size if stat.S_ISREG(info.st_mode) else 0
    return files, size


def remove_tree(path, log):
    """Remove PATH. Log and skip each entry that cannot go; return (files, bytes, failures).

    Files and bytes count what was actually removed (before minus what is left).
    """
    files, size = tree_totals(path)
    failed = []

    def writable(function, entry, error):
        parent = os.path.dirname(entry)
        with contextlib.suppress(OSError):
            os.chmod(parent, os.stat(parent).st_mode | stat.S_IWUSR | stat.S_IXUSR)
        try:
            function(entry)
        except FileNotFoundError:
            pass
        except OSError as again:
            failed.append(entry)
            log.write(f'{time.time():.0f}\tfailed\t{entry}\t0\t{again}\n')

    shutil.rmtree(path, onexc=writable)
    if failed:
        left_files, left_size = tree_totals(path)
        files, size = max(files - left_files, 0), max(size - left_size, 0)
        print(f'build janitor: {len(failed)} entr{"y" if len(failed) == 1 else "ies"} under '
              f'{path} could not be removed (see log)', file=sys.stderr)
    log.write(f'{time.time():.0f}\tremove-tree\t{path}\t{size}\tfiles={files}'
              + (f'\tfailed={len(failed)}' if failed else '') + '\n')
    return files, size, len(failed)


def rescue_goals(root, path, reason, log=None):
    """Move the saved goals and closure records under PATH into their stores; log each one.
    Return the goal store dir."""
    def note(line):
        if log is not None:
            log.write(line + '\n')
    destination, count = goal_store.rescue(root, path, reason=reason, log=note)
    if count:
        print(f'saved {count} goal file(s) from {path} to {destination}')
    closures = goal_store.rescue_closures(root, path, reason=reason, log=note)
    if closures:
        print(f'saved {closures} closure record(s) from {path} to '
              f'{Path(root) / goal_store.CLOSURES}')
    return destination


# --- worktree reaping ----------------------------------------------------------

# A checkout under .worktrees/ goes (`git worktree remove`, never --force) when it is clean
# (no tracked change), no live process or live registered run uses it, nothing in it changed
# for 6 h, nothing tracked on main names it, and its head is safe to drop: contained in
# origin/main, on a bench/* branch (the branch stays), or a detached head that a branch or
# remote ref still holds.
WORKTREE_REAP_IDLE_SECONDS = 6 * 3600
# Over 7 days idle, a checkout also goes when its work is put on origin first (no force):
# an unmerged branch is pushed; a detached head on no ref gets a pushed rescue/<name>-<date>
# branch; tracked changes and untracked non-ignored files are committed (git add -A) on a
# new rescue/<name>-<date> branch from HEAD and pushed. Every pushed branch is recorded in
# _build/janitor/rescued-worktrees.tsv (time, worktree, branch, head, pushed branch, commit, what).
RESCUE_IDLE_SECONDS = 7 * 24 * 3600
RESCUE_MAX_FILE_BYTES = 95 * 2**20  # GitHub refuses files over 100 MB: keep such checkouts
REAP_FREE_BYTES = 50 * GB  # the run watchdog reaps when free disk falls below this
SCRATCH_BRANCHES = ('bench/',)
# tools/bg and the run watchdog run from ops-tools (run_registry.md); the closed-set column
# takes early_verdict.py from ev-tools for worktrees older than it.
PROTECTED_WORKTREES = ('ops-tools', 'ev-tools')
WORKTREE_NAME = re.compile(r'\.worktrees/([A-Za-z0-9_.+-]+)')


def named_worktrees(root, main):
    """Worktree names that a tracked file at MAIN names (bench sets, harness pins, records)."""
    if not main:
        return frozenset()
    result = git(root, 'grep', '-hoIE', WORKTREE_NAME.pattern, main, '--')
    return frozenset(WORKTREE_NAME.search(line).group(1) for line in result.stdout.splitlines()
                     if WORKTREE_NAME.search(line))


def list_worktrees(root):
    """Rows of `git worktree list --porcelain` for checkouts under ROOT/.worktrees."""
    result = git(root, 'worktree', 'list', '--porcelain')
    if result.returncode:
        return []
    top = os.path.realpath(Path(root) / '.worktrees') + os.sep
    rows, row = [], None
    for line in result.stdout.splitlines():
        if line.startswith('worktree '):
            row = {'path': line[len('worktree '):], 'head': None, 'branch': None,
                   'locked': False, 'prunable': False}
            if os.path.realpath(row['path']).startswith(top):
                rows.append(row)
        elif row is None:
            continue
        elif line.startswith('HEAD '):
            row['head'] = line[len('HEAD '):]
        elif line.startswith('branch '):
            row['branch'] = line[len('branch '):].removeprefix('refs/heads/')
        elif line.startswith('locked'):
            row['locked'] = True
        elif line.startswith('prunable'):
            row['prunable'] = True
    return rows


def reflog_time(path):
    """Time of the last entry in the reflog file PATH, or 0. (The file's mtime is no
    activity signal: `git gc` reflog expiry rewrites every worktree's reflog.)"""
    with contextlib.suppress(OSError, ValueError, IndexError):
        with open(path, 'rb') as stream:
            stream.seek(max(os.fstat(stream.fileno()).st_size - 4096, 0))
            line = stream.read().rstrip(b'\n').rsplit(b'\n', 1)[-1]
        return float(line.split(b'\t', 1)[0].rsplit(b' ', 2)[1])
    return 0.0


def worktree_newest(path):
    """Newest mtime of the checkout top, its Git admin HEAD, and `_build` two levels deep,
    and the time of its last reflog entry."""
    candidates, logged = [path], 0.0
    with contextlib.suppress(OSError):
        text = (Path(path) / '.git').read_text()
        if text.startswith('gitdir: '):
            admin = Path(path) / text[len('gitdir: '):].strip()
            # Not the index: `git status` (this survey too) rewrites it.
            candidates.append(admin / 'HEAD')
            logged = reflog_time(admin / 'logs/HEAD')
    build = os.path.join(path, '_build')
    candidates.append(build)
    with contextlib.suppress(OSError):
        for name in os.listdir(build):
            entry = os.path.join(build, name)
            candidates.append(entry)
            if os.path.isdir(entry) and not os.path.islink(entry):
                with contextlib.suppress(OSError):
                    candidates += [os.path.join(entry, child) for child in os.listdir(entry)]
    newest = logged
    for candidate in candidates:
        with contextlib.suppress(OSError):
            newest = max(newest, os.lstat(candidate).st_mtime)
    return newest


def registry_paths(exclude=frozenset()):
    """Paths that live registered runs name (worktree, run dir, log, command), or None
    when the registry cannot be read (then nothing is reaped). Runs whose scheduler PID is
    in EXCLUDE (this process's own run) do not count."""
    try:
        import run_registry
        rows = run_registry.Registry(run_registry.default_store()).read()['runs'].values()
        paths = []
        for row in rows:
            if row['scheduler'].get('pid') in exclude:
                continue
            actors = [row['scheduler']] + row.get('jobs', [])
            if not (any(run_registry.live(a) for a in actors)
                    or any(not c.get('released') for c in row.get('claims', {}).values())):
                continue
            paths += [row[key] for key in ('worktree', 'run_dir', 'log', 'cwd')
                      if isinstance(row.get(key), str)]
            paths += [word for word in row.get('command', []) if isinstance(word, str)
                      and word.startswith('/')]
        return [os.path.realpath(path) for path in paths]
    except Exception as error:  # noqa: BLE001 - an unreadable registry keeps every worktree
        print(f'notice: build janitor: run registry unreadable ({error}); no worktree is reaped',
              file=sys.stderr)
        return None


def worktree_user(path, live, receipts, registered):
    """Why PATH is in use, else None."""
    user = live.user(path)
    if user:
        return f'live process {live.owners.get(user, "?")} uses {user}'
    under = receipts_under(receipts, path)
    if under:
        return 'the admission ledger names ' + under[0]
    prefix = os.path.realpath(path)
    for named in registered:
        if named == prefix or named.startswith(prefix + os.sep):
            return 'a live registered run names ' + named
    return None


def held_by_ref(root, head):
    """True when a branch or remote ref contains HEAD (dropping the checkout loses no commit)."""
    result = git(root, 'for-each-ref', '--count=1', '--format=%(refname)', '--contains', head,
                 'refs/heads', 'refs/remotes')
    return result.returncode == 0 and bool(result.stdout.strip())


def origin_heads(root):
    """{branch: commit} on origin (one `git ls-remote`), or None when origin is unreachable."""
    result = git(root, 'ls-remote', '--heads', 'origin')
    if result.returncode:
        return None
    heads = {}
    for line in result.stdout.splitlines():
        sha, _, ref = line.partition('\t')
        heads[ref.removeprefix('refs/heads/')] = sha
    return heads


def changed_paths(path):
    """(tracked changes, untracked non-ignored files) in the checkout PATH, or None on error."""
    status = git(path, 'status', '--porcelain=v1', '-z', '--untracked-files=all')
    if status.returncode:
        return None
    tracked, untracked = [], []
    entries = iter(status.stdout.split('\0'))
    for entry in entries:
        if not entry:
            continue
        (untracked if entry.startswith('??') else tracked).append(entry[3:])
        if entry[0] in 'RC':
            next(entries, None)  # the rename's source path
    return tracked, untracked


def classify_worktree(root, row, main, now, live, receipts, registered,
                      idle=WORKTREE_REAP_IDLE_SECONDS, named=frozenset(), creator=False,
                      remote=None):
    """Fill ROW with the facts and set action 'remove' or 'keep' with a reason. CREATOR (the
    run that made the checkout removes it at its end) also drops a checkout of a branch.
    A checkout idle over RESCUE_IDLE_SECONDS (not for a creator) also goes when its work
    can be pushed to origin first: ROW['rescue'] says how (see rescue_worktree). REMOTE is
    origin_heads()."""
    path = row['path']
    row['name'] = os.path.basename(path)
    row['newest'] = worktree_newest(path)
    changes = changed_paths(path)
    tracked, untracked = changes or ([], [])
    row['dirty'] = changes is None or bool(tracked)
    row['untracked'] = len(untracked)
    sizes = {}
    for name in tracked + untracked:
        with contextlib.suppress(OSError):
            info = os.lstat(os.path.join(path, name))
            row['newest'] = max(row['newest'], info.st_mtime)
            sizes[name] = info.st_size
    row['idle_hours'] = round((now - row['newest']) / 3600, 1)
    row['merged'] = bool(main and row['head'] and is_ancestor(root, row['head'], main))
    row['in_use'] = worktree_user(path, live, receipts, registered)
    row['rescue'] = None
    if row['merged']:
        row['kind'] = 'merged'
    elif row['branch'] and row['branch'].startswith(SCRATCH_BRANCHES):
        row['kind'] = 'scratch branch'
    elif row['branch'] is None and row['head'] and held_by_ref(root, row['head']):
        row['kind'] = 'detached'
    else:
        row['kind'] = 'unmerged branch' if row['branch'] else 'detached head on no ref'
    stale = not creator and now - row['newest'] >= RESCUE_IDLE_SECONDS
    unpushed = (row['kind'] == 'unmerged branch' and not creator
                and (remote or {}).get(row['branch']) != row['head'])
    large = sorted(name for name, size in sizes.items() if size > RESCUE_MAX_FILE_BYTES)
    if row['name'] in named and not creator:
        reason = 'named by a tracked file on main'
    elif row['name'] in PROTECTED_WORKTREES or row['locked']:
        reason = 'protected' if row['name'] in PROTECTED_WORKTREES else 'locked'
    elif row['prunable'] or not os.path.isdir(path):
        reason = 'missing checkout (git worktree prune)'
    elif changes is None:
        reason = 'git status failed'
    elif (row['dirty'] or untracked) and not stale:
        reason = 'tracked changes' if row['dirty'] else 'untracked files'
    elif row['in_use']:
        reason = row['in_use']
    elif now - row['newest'] < idle:
        reason = f'changed {row["idle_hours"]} h ago'
    elif (row['dirty'] or untracked) and large:
        reason = (f'{len(large)} changed file(s) over {RESCUE_MAX_FILE_BYTES // 2**20} MiB '
                  f'(origin refuses them), e.g. {large[0]}')
    elif (row['dirty'] or untracked or row['kind'] == 'detached head on no ref' or unpushed) \
            and remote is None and stale:
        reason = 'origin unreachable'
    elif row['dirty'] or untracked:
        reason, row['rescue'] = None, 'commit'
    elif row['kind'] == 'detached head on no ref':
        reason, row['rescue'] = (None, 'branch') if stale else (row['kind'], None)
    elif row['kind'] == 'unmerged branch' and not creator:
        if not stale:
            reason = row['kind']
        else:
            reason, row['rescue'] = None, 'push' if unpushed else None
    else:
        reason = None
    if not reason and row['kind'] == 'unmerged branch' and not row['rescue'] and not creator:
        row['kind'] = 'unmerged branch on origin'
    row.update(action='keep' if reason else 'remove',
               reason=reason or (row['kind'] + (f', rescue: {row["rescue"]}' if row['rescue'] else '')))
    return row


def rescue_name(root, name, now):
    """A free branch name `rescue/<name>-<YYYYMMDD>` (with -2, -3, ... when taken)."""
    base = f'rescue/{name}-{time.strftime("%Y%m%d", time.gmtime(now))}'
    candidate, count = base, 1
    while commit(root, 'refs/heads/' + candidate) or git(
            root, 'ls-remote', '--exit-code', '--heads', 'origin', candidate).returncode == 0:
        count += 1
        candidate = f'{base}-{count}'
    return candidate


def push(root, commit_id, branch):
    """Push COMMIT_ID to origin's BRANCH (no force) and confirm origin holds it. Return an
    error string or None."""
    result = git(root, 'push', '--quiet', 'origin', f'{commit_id}:refs/heads/{branch}')
    if result.returncode:
        return f'push {branch} failed: ' + (result.stderr.strip().splitlines() or ['?'])[-1]
    check = git(root, 'ls-remote', '--exit-code', 'origin', 'refs/heads/' + branch)
    if check.returncode or not check.stdout.startswith(commit_id):
        return f'push {branch}: origin does not hold {commit_id[:12]}'
    return None


def rescue_worktree(root, row, now, mapping):
    """Put the checkout's work on origin before it is removed. Return an error or None.
      push:   push the unmerged branch (no force).
      branch: detached head on no ref: create and push rescue/<name>-<date> at it.
      commit: tracked changes or untracked files: on a new branch rescue/<name>-<date> from
              HEAD, `git add -A` and commit everything (nothing discarded), push it; an
              unmerged branch under it is pushed too.
    Each pushed branch goes to MAPPING (rescued-worktrees.tsv)."""
    path, head, kind = row['path'], row['head'], row['rescue']
    stamp = time.strftime('%Y-%m-%dT%H:%M:%SZ', time.gmtime())

    def record(branch, commit_id, what):
        mapping.write(f'{stamp}\t{path}\t{row["branch"] or "detached"}\t{head}\t{branch}\t'
                      f'{commit_id}\t{what}\n')
        mapping.flush()

    if row['kind'] == 'unmerged branch' and kind in ('push', 'commit'):
        error = push(root, head, row['branch'])
        if error:
            return error
        record(row['branch'], head, 'pushed')
    if kind == 'push':
        return None
    branch = rescue_name(root, row['name'], now)
    if kind == 'branch':
        result = git(root, 'branch', branch, head)
        if result.returncode:
            return 'git branch: ' + result.stderr.strip()
        error = push(root, head, branch)
        if not error:
            record(branch, head, 'detached head')
        return error
    identity = ['-c', 'user.name=build janitor', '-c', 'user.email=build-janitor@localhost']
    steps = [('switch', '-q', '-c', branch), ('add', '-A'),
             (*identity, 'commit', '-q', '--no-verify', '-m',
              f'rescue: uncommitted work of worktree {row["name"]}\n\n'
              f'Worktree {path} on {row["branch"] or "detached " + head} was idle '
              f'{row["idle_hours"]} h; build_janitor committed every change before removing it.')]
    for step in steps:
        result = git(path, *step)
        if result.returncode:
            return f'git {step[-1] if step[0] == "-c" else step[0]}: ' + result.stderr.strip()
    rescued = commit(path, 'HEAD')
    error = push(root, rescued, branch)
    if not error:
        record(branch, rescued, 'uncommitted work')
    return error


def drop_checkout(root, path):
    return git(root, 'worktree', 'remove', path)


def remove_worktree(root, row, log, now=None, mapping=None):
    """Push the checkout's work to origin when ROW['rescue'] says so, rescue goals and closure
    records, then `git worktree remove` (no --force). Log it."""
    path = row['path']
    stamp = time.strftime('%Y-%m-%dT%H:%M:%SZ', time.gmtime())
    if row.get('rescue'):
        error = rescue_worktree(root, row, time.time() if now is None else now, mapping)
        if error:
            row.update(action='keep', reason='rescue: ' + error)
            log.write(f'{stamp}\tfailed\t{path}\t{row["branch"] or "detached"}\t{row["head"]}\t'
                      f'{row["reason"]}\n')
            return False
    rescue_goals(root, path, 'worktree reaper: ' + row['reason'])
    result = drop_checkout(root, path)
    if result.returncode:
        row.update(action='keep', reason='git worktree remove: ' + result.stderr.strip())
        log.write(f'{stamp}\tfailed\t{path}\t{row["branch"] or "detached"}\t{row["head"]}\t'
                  f'{row["reason"]}\n')
        return False
    log.write(f'{stamp}\tremoved\t{path}\t{row["branch"] or "detached"}\t{row["head"]}\t'
              f'{row["kind"]}, idle {row["idle_hours"]} h\n')
    log.flush()
    print(f'build janitor: removed worktree {path} ({row["kind"]}, idle {row["idle_hours"]} h)')
    return True


def reap_worktrees(root, *, apply, log_dir=None, main_ref='origin/main', now=None, proc='/proc',
                   idle=WORKTREE_REAP_IDLE_SECONDS, registered=None):
    """Classify every worktree under ROOT/.worktrees; with APPLY remove the reapable ones.
    Removals go to LOG_DIR/worktrees.log. Return the rows."""
    root = Path(root).resolve()
    log_dir = Path(log_dir) if log_dir else root / '_build/janitor'
    now = time.time() if now is None else now
    rows = list_worktrees(root)
    if not rows:
        return []
    if registered is None:
        registered = registry_paths(ancestors())
        if registered is None:
            return []
    main = commit(root, main_ref)
    named = named_worktrees(root, main)
    receipts = ledger_receipts(root)
    live = LivePaths.scan(root, proc, ancestors())
    remote = origin_heads(root)
    with ThreadPoolExecutor(max_workers=8) as pool:
        rows = list(pool.map(lambda row: classify_worktree(
            root, row, main, now, live, receipts, registered, idle, named, remote=remote), rows))
    if apply and any(row['action'] == 'remove' for row in rows):
        log_dir.mkdir(parents=True, exist_ok=True)
        live = LivePaths.scan(root, proc, ancestors())
        with open(log_dir / 'worktrees.log', 'a') as log, \
                open(log_dir / 'rescued-worktrees.tsv', 'a') as mapping:
            for row in rows:
                if row['action'] != 'remove':
                    continue
                user = worktree_user(row['path'], live, receipts, registered)
                if user:
                    row.update(action='keep', reason=user)
                elif worktree_newest(row['path']) > row['newest']:
                    row.update(action='keep', reason='changed during the janitor run')
                else:
                    remove_worktree(root, row, log, now, mapping)
    return rows


def ancestors(pid=None, proc='/proc'):
    """This process and its ancestors: a caller's own cwd never keeps its worktree."""
    found, pid = set(), pid or os.getpid()
    while pid and pid not in found:
        found.add(pid)
        try:
            with open(f'{proc}/{pid}/stat') as stream:
                pid = int(stream.read().rsplit(')', 1)[1].split()[1])
        except (OSError, ValueError, IndexError):
            break
    return found


def reap_when_low(root=None, threshold=REAP_FREE_BYTES):
    """The run watchdog's hook: reap worktrees when free disk is under THRESHOLD.
    Return message lines (empty when there is room or another reaper holds the lock)."""
    root = Path(root) if root else base_root()
    free = shutil.disk_usage(root).free
    if free >= threshold:
        return []
    log_dir = root / '_build/janitor'
    try:
        with exclusive(log_dir, '.worktrees.lock'):
            rows = reap_worktrees(root, apply=True, log_dir=log_dir)
    except SystemExit:
        return []
    removed = [row for row in rows if row['action'] == 'remove']
    after = shutil.disk_usage(root).free
    return [f'worktree reaper: free disk {human(free)} < {human(threshold)}: removed '
            f'{len(removed)} worktree(s), free now {human(after)} (log {log_dir / "worktrees.log"})']


# --- commands ------------------------------------------------------------------

def human(size):
    return f'{size / GB:.1f} GB'


@contextlib.contextmanager
def exclusive(log_dir, name='.lock'):
    log_dir.mkdir(parents=True, exist_ok=True)
    with open(log_dir / name, 'w') as lock:
        try:
            fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
        except OSError as error:
            if error.errno in (errno.EAGAIN, errno.EACCES):
                raise SystemExit('build janitor: another janitor holds ' + str(log_dir / name))
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
        failures = 0
        if args.apply:
            live = LivePaths.scan(janitor.root, janitor.proc, exclude)
            deleted = janitor.log_dir / f'deleted-{janitor.stamp}.tsv.gz'
            with gzip.open(deleted, 'wt') as log:
                freed, touched, failures = janitor.apply(plan, live, log)
            if touched:
                again = janitor.survey_runs(touched)
                runs = [r for r in runs if r['agent'] not in touched] + again
                budget = janitor.budget(runs)
        try:
            with exclusive(janitor.log_dir, '.worktrees.lock'):
                worktrees = reap_worktrees(janitor.root, apply=args.apply,
                                           log_dir=janitor.log_dir, main_ref=janitor.main_ref,
                                           now=janitor.now, proc=janitor.proc)
        except SystemExit as busy:
            print(busy, file=sys.stderr)
            worktrees = []
        janitor.write_json(Path(args.budget) if args.budget else janitor.build / 'BUDGET.json',
                           budget)
        janitor.write_json(janitor.log_dir / f'plan-{janitor.stamp}-{mode}.json',
                           {'mode': mode, 'root': str(janitor.root), 'main': plan['main'],
                            'freed': freed, 'rows': plan['rows'], 'worktrees': worktrees})
        lines = summary(plan, budget, mode, freed)
        removable = [row for row in worktrees if row['action'] == 'remove']
        if worktrees:
            lines.append(f'worktrees: {len(removable)} of {len(worktrees)} '
                         + ('removed' if args.apply else 'removable')
                         + f' (clean, idle {WORKTREE_REAP_IDLE_SECONDS // 3600} h, merged or '
                         f'measurement heads; idle {RESCUE_IDLE_SECONDS // 86400} days: '
                         f'{sum(bool(row.get("rescue")) for row in removable)} pushed to origin '
                         f'first; log {janitor.log_dir / "worktrees.log"})')
        if failures:
            lines.append(f'failed: {failures} target(s) could not be fully deleted; '
                         f'see {janitor.log_dir / f"deleted-{janitor.stamp}.tsv.gz"}')
        with open(janitor.log_dir / 'janitor.log', 'a') as log:
            for line in lines:
                log.write(f'{janitor.stamp}\t{mode}\t{line}\n')
        print('\n'.join(lines))
        print('plan: ' + str(janitor.log_dir / f'plan-{janitor.stamp}-{mode}.json'))
    return min(failures, 125)


def summary(plan, budget, mode, freed):
    lines = [f'build janitor ({mode}): total {human(budget["total_unique_bytes"])} of '
             f'{human(budget["total_budget_bytes"])}'
             + (' (OVER BUDGET)' if budget['total_over'] else '')]
    store = budget.get('goal_store')
    if store and store['over']:
        lines.append(f'over budget: goal store {store["path"]} {human(store["bytes"])} of '
                     f'{human(store["budget_bytes"])}')
    caches = budget.get('caches')
    if caches and caches['over']:
        lines.append(f'over budget: caches {caches["path"]} {human(caches["bytes"])} of '
                     f'{human(caches["budget_bytes"])} (run {caches["prune"]})')
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
        print(f'notice: build budget: ignoring unreadable {path}: {error}', file=sys.stderr)
        return 0
    agent = agent_of(environment, path.parent)
    row = rows.get(agent) if agent else None
    if not isinstance(row, dict) or not row.get('over') or row.get('protected'):
        return 0
    print(f'refused: resource guard: agent {agent} uses {human(row["unique_bytes"])} of its '
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
                saved = rescue_goals(root, path, 'cleanup_after_merge: ' + args.branch, log)
                files, size, _ = remove_tree(path, log)
                with open(janitor.log_dir / 'janitor.log', 'a') as summary_log:
                    if saved:
                        summary_log.write(f'{janitor.stamp}\tgoals\tsaved goals from {path} '
                                          f'to {saved}\n')
                    summary_log.write(f'{janitor.stamp}\tmerge\tremoved {path} '
                                      f'({files} files, {human(size)}) for {args.branch}\n')
                print(f'removed run dir {path} ({files} files, {human(size)} apparent)')
            else:
                for file, relative, _ in goal_store.goal_files(path):
                    print(f'would save goal {file}')
                for file, _, _ in goal_store.closure_files(path):
                    print(f'would save closure record {file}')
                print(f'would remove run dir {path}')
    return 0


def rescue_goals_command(args):
    root = Path(args.root) if args.root else base_root()
    if args.dry_run:
        for path in args.paths:
            for file, _, _ in goal_store.goal_files(path):
                print(f'would save goal {file}')
            for file, _, _ in goal_store.closure_files(path):
                print(f'would save closure record {file}')
        return 0
    log_dir = Path(args.log_dir) if args.log_dir else root / '_build/janitor'
    log_dir.mkdir(parents=True, exist_ok=True)
    stamp = time.strftime('%Y%m%dT%H%M%SZ', time.gmtime())
    with gzip.open(log_dir / f'deleted-{stamp}-goals.tsv.gz', 'at') as log:
        for path in args.paths:
            destination = rescue_goals(root, path, args.reason, log)
            if destination:
                with open(log_dir / 'janitor.log', 'a') as summary_log:
                    summary_log.write(f'{stamp}\tgoals\tsaved goals from {path} to '
                                      f'{destination}\n')
    return 0


def worktrees_command(args):
    """Report every worktree's facts and verdict; with --apply remove the reapable ones."""
    root = Path(args.root) if args.root else base_root()
    log_dir = Path(args.log_dir) if args.log_dir else root / '_build/janitor'
    with exclusive(log_dir, '.worktrees.lock'):
        rows = reap_worktrees(root, apply=args.apply, log_dir=log_dir, main_ref=args.main_ref,
                              idle=args.idle_hours * 3600)
    if args.json:
        Path(args.json).write_text(json.dumps(rows, indent=1, sort_keys=True) + '\n')
    for row in sorted(rows, key=lambda row: (row['action'], row['name'])):
        print(f'{row["action"]}\t{row["name"]}\t{row["branch"] or "detached " + (row["head"] or "?")[:12]}'
              f'\t{row["kind"]}\t{"dirty" if row["dirty"] else "clean"}\tidle {row["idle_hours"]} h'
              f'\t{row["reason"]}')
    removed = sum(row['action'] == 'remove' for row in rows)
    print(f'worktrees: {removed} of {len(rows)} ' + ('removed' if args.apply else 'removable'))
    return 0


def remove_worktree_command(args, sleep=time.sleep):
    """A creator's end-of-run removal: rescue goals and closure records, then `git worktree
    remove`. Refuses a dirty checkout or a head that no ref holds. With --wait, waits until no
    live process (other than this one's ancestors) or live registered run uses the checkout and
    nothing in it changed for --idle-minutes."""
    root = Path(args.root) if args.root else base_root()
    log_dir = Path(args.log_dir) if args.log_dir else root / '_build/janitor'
    status = 0
    for path in args.paths:
        path = os.path.realpath(path)
        [row] = [row for row in list_worktrees(root) if os.path.realpath(row['path']) == path] or [None]
        if row is None:
            print(f'remove-worktree: {path} is not a worktree under {root / ".worktrees"}', file=sys.stderr)
            status = 1
            continue
        while True:
            registered = registry_paths(ancestors())
            if registered is None:
                reason = 'run registry unreadable'
            else:
                row = classify_worktree(root, row, commit(root, args.main_ref), time.time(),
                                        LivePaths.scan(root, exclude=ancestors()),
                                        ledger_receipts(root), registered, args.idle_minutes * 60,
                                        creator=True)
                reason = None if row['action'] == 'remove' else row['reason']
            waiting = reason and (reason.startswith(('live process', 'a live registered run', 'changed '))
                                  or registered is None)
            if not (args.wait and waiting):
                break
            sleep(60)
        if reason:
            print(f'remove-worktree: kept {path}: {reason}', file=sys.stderr)
            status = 1
            continue
        log_dir.mkdir(parents=True, exist_ok=True)
        with open(log_dir / 'worktrees.log', 'a') as log:
            row['reason'] = 'end of run (' + row['kind'] + ')'
            if not remove_worktree(root, row, log):
                print(f'remove-worktree: kept {path}: {row["reason"]}', file=sys.stderr)
                status = 1
    return status


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
    goals = sub.add_parser('rescue-goals', help='move saved goals under paths into the store')
    goals.add_argument('paths', nargs='+')
    goals.add_argument('--reason', default='rescue-goals')
    trees = sub.add_parser('worktrees', help='report (with --apply remove) reapable worktrees')
    trees.add_argument('--idle-hours', type=float, default=WORKTREE_REAP_IDLE_SECONDS / 3600)
    trees.add_argument('--json', help='write every row to this file')
    remove = sub.add_parser('remove-worktree', help='remove worktrees a run created, at its end')
    remove.add_argument('paths', nargs='+')
    remove.add_argument('--wait', action='store_true',
                        help='wait until no live process or run uses the checkout')
    remove.add_argument('--idle-minutes', type=float, default=0,
                        help='also wait until nothing in it changed for this long')
    args = parser.parse_args(argv)
    if args.apply and args.dry_run:
        parser.error('--apply and --dry-run exclude each other')
    if args.command == 'admit':
        return admit(args)
    if args.command == 'in-use':
        return in_use(args)
    if args.command == 'branch-items':
        return branch_items(args)
    if args.command == 'rescue-goals':
        return rescue_goals_command(args)
    if args.command == 'worktrees':
        return worktrees_command(args)
    if args.command == 'remove-worktree':
        return remove_worktree_command(args)
    return run(args)


if __name__ == '__main__':
    sys.exit(main())
