"""Reuse a digest only while the complete file identity remains unchanged.

The persistent store is optional. Records live in `CACHE_ROOT/<key[:2]>/<key>.json`
and are pruned by age, by recorded identity, and by a count and size cap. A
removed record only costs a rehash; every hit keeps the exact identity checks.
"""
from contextlib import contextmanager, suppress
from contextvars import ContextVar
import fcntl
import hashlib
import json
import os
from pathlib import Path
import re
import stat
import tempfile
import time

_FORCE = ContextVar('force_binding_hash', default=False)
_DIGESTS = {}
CACHE_ROOT = Path.home() / '.cache/zesislar/binding-digests-v2'
# The flat v1 store beside CACHE_ROOT grew without bound. It is never read; prune drains it.
LEGACY_NAME = 'binding-digests-v1'
MAX_AGE_SECONDS = 2 * 86400
MAX_ENTRIES = 100_000
MAX_BYTES = 10 ** 9
PRUNE_INTERVAL_SECONDS = 3600
LEGACY_BATCH = 20_000
LEGACY_SECONDS = 2.0
TEMP_AGE_SECONDS = 3600
RECORD = re.compile(r'([0-9a-f]{64})\.(json|lock)')
_NEXT_PRUNE = {}
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
        shard = root / key[:2]
        shard.mkdir(mode=0o700, exist_ok=True)
        if shard.is_symlink() or not _protected(shard.stat(), directory=True):
            raise OSError('The digest cache shard is not private.')
        descriptor = os.open(shard / (key + '.lock'),
                             os.O_RDWR | os.O_CREAT | os.O_NOFOLLOW, 0o600)
        if not _protected(os.fstat(descriptor)):
            raise OSError('The digest cache lock is not private.')
        fcntl.flock(descriptor, fcntl.LOCK_EX)
        path = shard / (key + '.json')
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
        # This cache is disposable. Atomic replacement protects readers.
        # Missing or malformed records require a validated rehash.
        os.replace(name, path)
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
                with suppress(OSError):
                    os.utime(record)  # Age counts from the last use.
            else:
                value = _hash(path, before)
                if identity(path) != before:
                    raise ValueError('A bound file changed during validation: ' + str(path))
                if record is not None:
                    try:
                        _publish(record, context, value)
                    except OSError:
                        COUNTERS['persistent_unavailable'] += 1
        if record is not None:  # The store exists and passed its privacy checks.
            maybe_prune(Path(CACHE_ROOT), _scheduled_prune)
    if identity(path) != before:
        raise ValueError('A bound file changed during validation: ' + str(path))
    _DIGESTS[key] = value
    if hit is not None:
        COUNTERS[hit] += 1
    return value


def release_process_cache():
    """Drop optional process hits. Every later lookup keeps its exact checks."""
    count=len(_DIGESTS)
    _DIGESTS.clear()
    return count


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


# --- bounded storage -----------------------------------------------------------

def new_stats():
    return {'kept': 0, 'removed': 0, 'busy': 0, 'removed_bytes': 0, 'legacy_removed': 0}


def remove_file(path, stats, key='removed', info=None):
    """Unlink one file (never following a link) and count it under `key`."""
    try:
        info = info or os.lstat(path)
        os.unlink(path)
    except FileNotFoundError:
        return
    if key is not None:
        stats[key] += 1
    stats['removed_bytes'] += info.st_blocks * 512


def _remove_unit(record, lock, stats):
    """Delete one record and its lock unless a process holds the lock now."""
    try:
        descriptor = os.open(lock, os.O_RDWR | os.O_NOFOLLOW)
    except OSError:
        descriptor = None
    try:
        if descriptor is not None:
            try:
                fcntl.flock(descriptor, fcntl.LOCK_EX | fcntl.LOCK_NB)
            except BlockingIOError:
                stats['busy'] += 1
                return
        remove_file(record, stats)
        remove_file(lock, stats, key=None)
    finally:
        if descriptor is not None:
            os.close(descriptor)


def prune_records(shards, *, now, expired, stats, max_age=None, max_entries=None,
                  max_bytes=None):
    """Bound the `<key>.json`/`<key>.lock` records in the given shard directories.

    Remove records unused for `max_age`, then the oldest beyond the count and byte
    caps, then those `expired(record)` names as unreachable. Remove crash leftovers
    and orphan locks after an hour. A lock held by a live process keeps its record.
    """
    max_age = MAX_AGE_SECONDS if max_age is None else max_age
    max_entries = MAX_ENTRIES if max_entries is None else max_entries
    max_bytes = MAX_BYTES if max_bytes is None else max_bytes
    units = {}
    for shard in shards:
        try:
            listing = os.scandir(shard)
        except OSError:
            continue
        with listing:
            for entry in listing:
                try:
                    info = entry.stat(follow_symlinks=False)
                except OSError:
                    continue
                match = RECORD.fullmatch(entry.name)
                if match is None:
                    if not stat.S_ISDIR(info.st_mode) and now - info.st_mtime > TEMP_AGE_SECONDS:
                        remove_file(entry.path, stats, info=info)
                    continue
                unit = units.setdefault(os.path.join(shard, match[1]),
                                        {'json': None, 'lock': 0.0, 'bytes': 0})
                unit[match[2]] = info.st_mtime
                unit['bytes'] += info.st_blocks * 512
    survivors, count, size = [], 0, 0
    rows = sorted(units.items(), key=lambda row: max(row[1]['json'] or 0, row[1]['lock']),
                  reverse=True)
    for stem, unit in rows:
        used = unit['json'] if unit['json'] is not None else unit['lock']
        limit = max_age if unit['json'] is not None else TEMP_AGE_SECONDS
        if (now - used <= limit and count < max_entries and size + unit['bytes'] <= max_bytes
                and (unit['json'] is None or not expired(stem + '.json'))):
            count += 1
            size += unit['bytes']
            survivors.append(stem)
        else:
            _remove_unit(stem + '.json', stem + '.lock', stats)
    stats['kept'] += len(survivors)
    return stats


def drain(directory, stats, limit=None, deadline=None):
    """Delete files of a retired store; remove the emptied directories.

    Stop after `limit` files or at the monotonic `deadline` (None: no bound).
    Return how many deletions remain in the limit.
    """
    try:
        listing = os.scandir(directory)
    except OSError:
        return limit
    with listing:
        for entry in listing:
            if ((limit is not None and limit <= 0) or
                    (deadline is not None and time.monotonic() > deadline)):
                return limit
            try:
                info = entry.stat(follow_symlinks=False)
            except OSError:
                continue
            if stat.S_ISDIR(info.st_mode):
                limit = drain(entry.path, stats, limit, deadline)
            else:
                remove_file(entry.path, stats, key='legacy_removed', info=info)
                if limit is not None:
                    limit -= 1
    with suppress(OSError):
        os.rmdir(directory)
    return limit


def _identity_gone(record):
    """True when the file a record names no longer has the recorded identity."""
    try:
        descriptor = os.open(record, os.O_RDONLY | os.O_NOFOLLOW)
        with os.fdopen(descriptor, 'rb') as stream:
            context = json.loads(stream.read(16385))['context']
        current = identity(Path(context['path']))
        return [list(current[0]), list(current[1])] != [context['lstat'], context['stat']]
    except (OSError, ValueError, TypeError, KeyError):
        return True


def prune(*, now=None, legacy_limit=None, legacy_seconds=None):
    """Bound the digest store and drain the retired flat v1 store beside it.

    `legacy_limit` and `legacy_seconds` bound the drain (None: drain it all).
    """
    root = Path(CACHE_ROOT)
    now = time.time() if now is None else now
    stats = new_stats()
    if root.is_dir() and not root.is_symlink():
        shards = [entry.path for entry in os.scandir(root)
                  if entry.is_dir(follow_symlinks=False)]
        prune_records(shards, now=now, expired=_identity_gone, stats=stats)
    legacy = root.parent / LEGACY_NAME
    if legacy.is_dir() and not legacy.is_symlink():
        deadline = None if legacy_seconds is None else time.monotonic() + legacy_seconds
        drain(legacy, stats, legacy_limit, deadline)
    return stats


def _scheduled_prune():
    # A lookup never waits long: the scheduled drain of a retired store is bounded.
    return prune(legacy_limit=LEGACY_BATCH, legacy_seconds=LEGACY_SECONDS)


def maybe_prune(root, run):
    """Run `run()` at most once an hour per store and process, never concurrently.

    The per-process check is a clock read; a stamp file shares the hour across
    processes. Pruning is best effort: an unavailable store skips it.
    """
    now = time.monotonic()
    if _NEXT_PRUNE.get(str(root), 0.0) > now:
        return None
    _NEXT_PRUNE[str(root)] = now + PRUNE_INTERVAL_SECONDS
    stamp = root / '.pruned'

    def fresh():
        try:
            return time.time() - stamp.stat().st_mtime < PRUNE_INTERVAL_SECONDS
        except FileNotFoundError:
            return False
    try:
        if fresh():
            return None
        info = root.lstat()
        if not stat.S_ISDIR(info.st_mode) or info.st_uid != os.getuid():
            return None
        descriptor = os.open(root / '.prune.lock', os.O_RDWR | os.O_CREAT | os.O_NOFOLLOW, 0o600)
        try:
            fcntl.flock(descriptor, fcntl.LOCK_EX | fcntl.LOCK_NB)
            if fresh():
                return None
            stamp.touch(mode=0o600)
            os.utime(stamp)
            return run()
        finally:
            os.close(descriptor)
    except OSError:
        return None
