"""Reuse a digest only while the complete file identity remains unchanged."""
from contextlib import contextmanager
from contextvars import ContextVar
import hashlib
import os
from pathlib import Path

_FORCE = ContextVar('force_binding_hash', default=False)
_DIGESTS = {}


def identity(path):
    def fields(info):
        return (info.st_dev, info.st_ino, info.st_size, info.st_mtime_ns,
                info.st_ctime_ns, info.st_mode)
    return fields(path.lstat()), fields(path.stat())


def digest(path):
    path = Path(path)
    before = identity(path)
    key = (str(path.absolute()), before)
    if not _FORCE.get() and key in _DIGESTS:
        value = _DIGESTS[key]
    else:
        with path.open('rb') as stream:
            opened=os.fstat(stream.fileno())
            fields=lambda info:(info.st_dev,info.st_ino,info.st_size,info.st_mtime_ns,info.st_ctime_ns,info.st_mode)
            if fields(opened)!=before[1]:
                raise ValueError('A bound file changed before hashing: '+str(path))
            value = hashlib.file_digest(stream, 'sha256').hexdigest()
            if fields(os.fstat(stream.fileno()))!=before[1]:
                raise ValueError('A bound file changed during validation: '+str(path))
    if identity(path) != before:
        raise ValueError('A bound file changed during validation: ' + str(path))
    _DIGESTS[key] = value
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
