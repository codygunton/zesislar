"""Share exact, source-context-bound coqdep answers for one supplier."""
from contextlib import contextmanager
import fcntl
import hashlib
import json
import os
from pathlib import Path
import tempfile
import time

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
        descriptor = os.open(path, os.O_WRONLY | os.O_CREAT | os.O_APPEND | os.O_NOFOLLOW, 0o600)
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
        descriptor = os.open(self.root / (key + '.lock'),
                             os.O_RDWR | os.O_CREAT | os.O_NOFOLLOW, 0o600)
        try:
            fcntl.flock(descriptor, fcntl.LOCK_EX)
            yield
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
        path = self.root / (key + '.json')
        with self.locked(key):
            entry = self.read(path, context, instance)
            if entry is not None and self.context(instance, module, request) == context:
                self.record('cache_hits', module=module, key=key)
                return entry, request
            self.record('cache_misses', module=module, key=key)
            entry, actual_request = produce(module, request)
            require(actual_request == request)
            selected = dict(mapping=entry['mapping'], canonical=entry['canonical'],
                            source=file_binding(entry['source']), object=file_binding(entry['object']))
            require(self.context(instance, module, request) == context)
            descriptor, temporary = tempfile.mkstemp(prefix=key + '.', dir=self.root)
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
