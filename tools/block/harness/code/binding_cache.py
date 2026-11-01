"""Reuse a digest only while the complete file identity remains unchanged."""
from contextlib import contextmanager
from contextvars import ContextVar
import fcntl
import hashlib
import json
import os
from pathlib import Path
import re
import stat
import tempfile

_FORCE = ContextVar('force_binding_hash', default=False)
_DIGESTS = {}
CACHE_ROOT = Path.home() / '.cache/zesislar/binding-digests-v1'
_SCHEMA = 'binding.digest.full-identity.v1'
COUNTERS = {'process_hits': 0, 'persistent_hits': 0, 'hashes': 0,
            'persistent_unavailable': 0, 'invalid_records': 0}


def _encoded(value):
    return json.dumps(value, sort_keys=True, separators=(',', ':')).encode()


def _fields(info):
    return (info.st_dev, info.st_ino, info.st_size, info.st_mtime_ns,
            info.st_ctime_ns, info.st_mode)


def _protected(info, *, directory=False):
    kind = stat.S_ISDIR if directory else stat.S_ISREG
    return (kind(info.st_mode) and info.st_uid == os.getuid() and
            info.st_mode & 0o077 == 0 and (directory or info.st_nlink == 1))


@contextmanager
def _persistent(context):
    """Serialize one identity key in protected, optional cache storage."""
    descriptor = None
    try:
        root = Path(CACHE_ROOT)
        root.mkdir(mode=0o700, parents=True, exist_ok=True)
        if root.is_symlink() or not _protected(root.stat(), directory=True):
            raise OSError('The digest cache directory is not private.')
        key = hashlib.sha256(_encoded(context)).hexdigest()
        descriptor = os.open(root / (key + '.lock'),
                             os.O_RDWR | os.O_CREAT | os.O_NOFOLLOW, 0o600)
        if not _protected(os.fstat(descriptor)):
            raise OSError('The digest cache lock is not private.')
        fcntl.flock(descriptor, fcntl.LOCK_EX)
        path = root / (key + '.json')
    except OSError:
        if descriptor is not None:
            os.close(descriptor)
        COUNTERS['persistent_unavailable'] += 1
        yield None
        return
    try:
        yield path
    finally:
        os.close(descriptor)


def _unique(pairs):
    result = {}
    for key, value in pairs:
        if key in result:
            raise ValueError('The digest cache record repeats a field.')
        result[key] = value
    return result


def _read_persistent(path, context):
    try:
        descriptor = os.open(path, os.O_RDONLY | os.O_NOFOLLOW)
        with os.fdopen(descriptor, 'rb') as stream:
            before = os.fstat(stream.fileno())
            if not _protected(before) or before.st_size > 16384:
                raise ValueError('The digest cache record is not private or bounded.')
            payload = stream.read()
            if _fields(os.fstat(stream.fileno())) != _fields(before):
                raise ValueError('The digest cache record changed during reading.')
        row = json.loads(payload, object_pairs_hook=_unique)
        if (not isinstance(row, dict) or set(row) != {'schema', 'context', 'sha256'} or
                row['schema'] != _SCHEMA or _encoded(row['context']) != _encoded(context) or
                not isinstance(row['sha256'], str) or
                re.fullmatch('[0-9a-f]{64}', row['sha256']) is None):
            raise ValueError('The digest cache record is invalid.')
        return row['sha256']
    except FileNotFoundError:
        return None
    except (OSError, ValueError, TypeError):
        COUNTERS['invalid_records'] += 1
        return None


def _publish(path, context, value):
    descriptor, name = tempfile.mkstemp(prefix='.digest-', dir=path.parent)
    try:
        with os.fdopen(descriptor, 'wb') as stream:
            stream.write(_encoded(dict(schema=_SCHEMA, context=context, sha256=value)))
            stream.flush()
            os.fsync(stream.fileno())
        os.replace(name, path)
        directory = os.open(path.parent, os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW)
        try:
            os.fsync(directory)
        finally:
            os.close(directory)
    finally:
        if os.path.exists(name):
            os.unlink(name)



def identity(path):
    def fields(info):
        return (info.st_dev, info.st_ino, info.st_size, info.st_mtime_ns,
                info.st_ctime_ns, info.st_mode)
    return fields(path.lstat()), fields(path.stat())


def _hash(path, before):
    with path.open('rb') as stream:
        fields = lambda info: (info.st_dev, info.st_ino, info.st_size,
                               info.st_mtime_ns, info.st_ctime_ns, info.st_mode)
        if fields(os.fstat(stream.fileno())) != before[1]:
            raise ValueError('A bound file changed before hashing: ' + str(path))
        value = hashlib.file_digest(stream, 'sha256').hexdigest()
        if fields(os.fstat(stream.fileno())) != before[1]:
            raise ValueError('A bound file changed during validation: ' + str(path))
    COUNTERS['hashes'] += 1
    return value


def digest(path):
    path = Path(path)
    before = identity(path)
    key = (str(path.absolute()), before)
    hit = None
    if _FORCE.get():
        value = _hash(path, before)
    elif key in _DIGESTS:
        value = _DIGESTS[key]
        hit = 'process_hits'
    else:
        context = {'path': key[0], 'lstat': list(before[0]), 'stat': list(before[1])}
        with _persistent(context) as record:
            # The lock wait can overlap a mutation or replacement.
            if identity(path) != before:
                raise ValueError('A bound file changed during validation: ' + str(path))
            value = _read_persistent(record, context) if record else None
            if value is not None:
                hit = 'persistent_hits'
            else:
                value = _hash(path, before)
                if identity(path) != before:
                    raise ValueError('A bound file changed during validation: ' + str(path))
                if record is not None:
                    try:
                        _publish(record, context, value)
                    except OSError:
                        COUNTERS['persistent_unavailable'] += 1
    if identity(path) != before:
        raise ValueError('A bound file changed during validation: ' + str(path))
    _DIGESTS[key] = value
    if hit is not None:
        COUNTERS[hit] += 1
    return value


@contextmanager
def force_hashing(enabled=True):
    token = _FORCE.set(_FORCE.get() or enabled)
    try:
        yield
    finally:
        _FORCE.reset(token)


def resolve_input(path, parents):
    """Resolve every input with a fresh, per-operation parent lookup."""
    path = Path(path).absolute()
    parent = str(path.parent)
    if parent not in parents:
        parents[parent] = path.parent.resolve()
    resolved = parents[parent] / path.name
    return resolved.resolve() if resolved.is_symlink() else resolved
