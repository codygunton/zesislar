"""Share exact, source-context-bound coqdep answers for one supplier.

Records live in `CACHE_ROOT/<supplier sha256>/<key[:2]>/<key>.json`. The store is
optional and bounded: `prune` removes records by age, by missing inputs, and by a
count and size cap. A removed record only costs one coqdep query.
"""
from contextlib import contextmanager, suppress
import fcntl
import hashlib
import json
import os
from pathlib import Path
import stat
import tempfile
import time

import binding_cache
from binding_cache import digest

CACHE_ROOT = Path.home() / '.cache/zesislar/supplier-import-resolution'
SCHEMA = 'compiled-library.supplier-resolution.v1'


def encoded(value):
    return json.dumps(value, sort_keys=True, separators=(',', ':')).encode()


def require(condition):
    if not condition:
        raise ValueError('A supplier resolution cache binding changed.')


def file_binding(path):
    path = Path(path)
    return {'path': str(path), 'sha256': digest(path)}


class SupplierResolutionCache:
    def __init__(self, supplier):
        require(set(supplier) == {'path', 'sha256'} and
                len(supplier['sha256']) == 64 and
                all(word in '0123456789abcdef' for word in supplier['sha256']))
        require(file_binding(supplier['path']) == supplier)
        self.supplier = dict(supplier)
        binding_cache.maybe_prune(Path(CACHE_ROOT), prune)
        self.root = CACHE_ROOT / supplier['sha256']
        self.root.mkdir(parents=True, exist_ok=True, mode=0o700)
        require(not self.root.is_symlink() and self.root.stat().st_uid == os.getuid())
        self.counters = {'logical_lookups': 0, 'cache_hits': 0,
                         'cache_misses': 0, 'coqdep_invocations': 0}
        self.tree = None
        self.tree_guards = []

    def tree_state(self, path):
        try:
            info = path.lstat()
        except FileNotFoundError:
            return None
        state = [info.st_dev, info.st_ino, info.st_mode, info.st_mtime_ns, info.st_ctime_ns]
        if path.is_symlink():
            state.extend([str(path.resolve()), path.exists()])
            if path.exists():
                target = path.stat()
                state.extend([target.st_dev, target.st_ino, target.st_mode,
                              target.st_mtime_ns, target.st_ctime_ns])
        return state

    def inventory(self, instance):
        # Directory identities detect additions, removals, and replacements. Selected
        # source/object bytes are checked separately on every hit.
        if self.tree is not None and all(self.tree_state(path) == state
                                         for path, state in self.tree_guards):
            return self.tree
        inventory, guards = [], {}
        for mapping in instance.roots:
            root = Path(mapping['root'])
            guards[root] = self.tree_state(root)
            candidates = []
            if root.is_dir():
                for path in sorted(root.rglob('*')):
                    # Path.rglob does not traverse directory aliases. Resolve these
                    # uncommon contexts with coqdep instead of using a partial tree.
                    if path.is_symlink() and path.is_dir():
                        self.tree = None
                        return None
                    if path.is_dir() or path.is_symlink():
                        guards[path] = self.tree_state(path)
                    if path.suffix in {'.v', '.vo', '.vos', '.vok', '.vio'} or path.is_symlink():
                        candidates.append([str(path), str(path.resolve()), path.is_symlink(), path.exists()])
            inventory.append([mapping, root.is_dir(), candidates])
        require(all(self.tree_state(path) == state for path, state in guards.items()))
        self.tree_guards = list(guards.items())
        self.tree = hashlib.sha256(encoded(inventory)).hexdigest()
        return self.tree

    def record(self, event, **details):
        self.counters[event] += 1
        row = dict(time_ns=time.time_ns(), event=event, pid=os.getpid(), **details)
        path = self.root / ('events-' + str(os.getpid()) + '.jsonl')
        flags = os.O_WRONLY | os.O_CREAT | os.O_APPEND | os.O_NOFOLLOW
        try:
            descriptor = os.open(path, flags, 0o600)
        except FileNotFoundError:  # prune removed an idle supplier directory
            self.root.mkdir(parents=True, exist_ok=True, mode=0o700)
            descriptor = os.open(path, flags, 0o600)
        try:
            os.write(descriptor, encoded(row) + b'\n')
        finally:
            os.close(descriptor)

    def context(self, instance, module, request):
        require(file_binding(self.supplier['path']) == self.supplier)
        require(digest(instance.coqdep) == instance.tool_sha256)
        origin = request['origin']
        if 'path' in origin:
            require(file_binding(origin['path']) == origin)
        import check_data_only_lemmas
        implementations = [Path(__file__), Path(__file__).with_name('installed_mappings.py'),
                           Path(check_data_only_lemmas.__file__)]
        flags = instance.dependency_flags(origin)
        # Relative search paths depend on the fresh query directory. Do not reuse them.
        for index, flag in enumerate(flags[:-1]):
            if flag in {'-I', '-coqlib'} and not Path(flags[index + 1]).is_absolute():
                return None
        inventory = self.inventory(instance)
        if inventory is None:
            return None
        return dict(schema=SCHEMA, supplier=self.supplier,
                    resolver=file_binding(instance.coqdep),
                    implementations=[file_binding(path) for path in implementations],
                    module=module, request=request, flags=flags,
                    inventory_sha256=inventory,
                    environment={'COQPATH': '', 'LANG': 'C', 'LC_ALL': 'C', 'LC_CTYPE': 'C'},
                    query_directory='fresh_private_directory')

    @contextmanager
    def locked(self, key):
        """Yield the record path under the key's lock, or None when the store is unavailable."""
        try:
            shard = self.root / key[:2]
            shard.mkdir(parents=True, exist_ok=True, mode=0o700)
            descriptor = os.open(shard / (key + '.lock'),
                                 os.O_RDWR | os.O_CREAT | os.O_NOFOLLOW, 0o600)
        except OSError:
            yield None
            return
        try:
            fcntl.flock(descriptor, fcntl.LOCK_EX)
            yield shard / (key + '.json')
        finally:
            os.close(descriptor)

    def read(self, path, context, instance):
        try:
            require(not path.is_symlink())
            row = json.loads(path.read_text())
            require(set(row) == {'context', 'selected'} and row['context'] == context)
            selected = row['selected']
            require(set(selected) == {'mapping', 'canonical', 'source', 'object'})
            matches = [entry for entry in instance.entries
                       if entry['canonical'] == selected['canonical'] and
                       entry['mapping'] == selected['mapping'] and
                       str(entry['source']) == selected['source']['path'] and
                       str(entry['object']) == selected['object']['path']]
            require(len(matches) == 1)
            require(file_binding(selected['source']['path']) == selected['source'])
            require(file_binding(selected['object']['path']) == selected['object'])
            return matches[0]
        except (OSError, ValueError, KeyError, TypeError):
            return None

    def query(self, instance, module, request, produce):
        context = self.context(instance, module, request)
        if context is None:
            self.record('cache_misses', module=module, reason='uncached_query_context')
            return produce(module, request)
        key = hashlib.sha256(encoded(context)).hexdigest()
        with self.locked(key) as path:
            if path is None:
                self.record('cache_misses', module=module, key=key, reason='store_unavailable')
                return produce(module, request)
            entry = self.read(path, context, instance)
            if entry is not None and self.context(instance, module, request) == context:
                self.record('cache_hits', module=module, key=key)
                with suppress(OSError):
                    os.utime(path)  # Age counts from the last use.
                return entry, request
            self.record('cache_misses', module=module, key=key)
            entry, actual_request = produce(module, request)
            require(actual_request == request)
            selected = dict(mapping=entry['mapping'], canonical=entry['canonical'],
                            source=file_binding(entry['source']), object=file_binding(entry['object']))
            require(self.context(instance, module, request) == context)
            descriptor, temporary = tempfile.mkstemp(prefix=key + '.', dir=path.parent)
            try:
                with os.fdopen(descriptor, 'wb') as stream:
                    stream.write(encoded(dict(context=context, selected=selected)) + b'\n')
                    stream.flush()
                    os.fsync(stream.fileno())
                os.replace(temporary, path)
            finally:
                if os.path.exists(temporary):
                    os.unlink(temporary)
            return entry, actual_request


def _inputs_gone(record):
    """True when a file that a record binds no longer exists."""
    try:
        descriptor = os.open(record, os.O_RDONLY | os.O_NOFOLLOW)
        with os.fdopen(descriptor, 'rb') as stream:
            row = json.loads(stream.read())
        context, selected = row['context'], row['selected']
        paths = [context['supplier']['path'], context['resolver']['path'],
                 selected['source']['path'], selected['object']['path']]
        return not all(isinstance(path, str) and os.path.exists(path) for path in paths)
    except (OSError, ValueError, TypeError, KeyError):
        return True


def prune(*, now=None):
    """Bound every supplier's records; drop flat v1 records, old event logs, idle suppliers."""
    root = Path(CACHE_ROOT)
    now = time.time() if now is None else now
    stats = binding_cache.new_stats()
    if not root.is_dir() or root.is_symlink():
        return stats
    shards, idle = [], []
    for supplier in os.scandir(root):
        if not supplier.is_dir(follow_symlinks=False):
            continue
        if now - supplier.stat(follow_symlinks=False).st_mtime > binding_cache.MAX_AGE_SECONDS:
            idle.append(supplier.path)
        with os.scandir(supplier.path) as listing:
            for entry in listing:
                info = entry.stat(follow_symlinks=False)
                if stat.S_ISDIR(info.st_mode):
                    shards.append(entry.path)
                elif (binding_cache.RECORD.fullmatch(entry.name) or
                      now - info.st_mtime > (binding_cache.MAX_AGE_SECONDS
                                             if entry.name.startswith('events-')
                                             else binding_cache.TEMP_AGE_SECONDS)):
                    # Flat records are the retired unsharded layout.
                    binding_cache.remove_file(entry.path, stats, key='legacy_removed', info=info)
    binding_cache.prune_records(shards, now=now, expired=_inputs_gone, stats=stats)
    for supplier in idle:
        for shard in os.scandir(supplier):
            if shard.is_dir(follow_symlinks=False):
                with suppress(OSError):
                    os.rmdir(shard.path)
        with suppress(OSError):
            os.rmdir(supplier)
    return stats


def profile_supplier(profile_binding):
    """Read the governing profile without repeating supplier validation."""
    if profile_binding is None:
        return None
    from entry_chain import read_bound
    return read_bound(profile_binding).get('supplier_ready')
