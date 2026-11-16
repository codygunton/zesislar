"""The saved-goal store `_build/goals/<function>/<case>/<tag>/`.

Saved residual goals are small `.v` files that rule work replays in scratch. Run dirs come and go
(`tools/cleanup_after_merge.sh`, the build janitor); the store does not. Neither tool deletes
anything under `_build/goals/`. The janitor reports its size against its own budget
(GOAL_STORE_BUDGET_BYTES) in `_build/BUDGET.json`.

Each tag dir holds the goal files and `MANIFEST.json` (head, bank, command, date, sources).
`tools/save_goal.py` saves goals by hand; `rescue()` moves saved goals out of a run dir that
cleanup is about to delete, into `_build/goals/<function or _rescued>/<run dir>/rescued-<stamp>/`.

Closure records (`CLOSURE.json`, `NOT-CLOSED.json` from tools/closure_cert.py) live beside it in
`_build/closures/<function>/<case>/<run>/`; `rescue_closures()` moves them there the same way.
"""

import contextlib
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import stat
import time

STORE = Path('_build/goals')
GOAL_MAX_BYTES = 1 << 20
GOAL_STORE_BUDGET_BYTES = 2 * 10 ** 9
MANIFEST = 'MANIFEST.json'
RESCUED_FUNCTION = '_rescued'
CLOSURES = Path('_build/closures')
CLOSURE_NAMES = frozenset(('CLOSURE.json', 'NOT-CLOSED.json'))
# Build trees copy every source file, GoalDomain.v included; they hold no saved goals.
SKIP_DIRS = frozenset(('default', 'bank', 'banks', 'IMPORT-RESOLUTION', '.git'))
SEGMENT = re.compile(r'^[A-Za-z0-9_][A-Za-z0-9_.@+-]*$')


def is_goal(relative):
    """True for a saved-goal file: `*Goal*.v` (extract.py writes Goal<k>.v) or `goals/**/*.v`."""
    parts = Path(relative).parts
    if not parts or not parts[-1].endswith('.v') or SKIP_DIRS.intersection(parts[:-1]):
        return False
    return 'Goal' in parts[-1] or 'goals' in parts[:-1]


def goal_files(directory):
    """Yield (path, relative path, size) of the regular saved-goal files under DIRECTORY."""
    for current, subdirectories, names in os.walk(directory):
        subdirectories[:] = sorted(d for d in subdirectories if d not in SKIP_DIRS)
        for name in sorted(names):
            path = os.path.join(current, name)
            relative = os.path.relpath(path, directory)
            if not is_goal(relative):
                continue
            with contextlib.suppress(OSError):
                info = os.lstat(path)
                if stat.S_ISREG(info.st_mode):
                    yield path, relative, info.st_size


def check_segment(value, what):
    if not SEGMENT.match(value or '') or value in ('.', '..'):
        raise ValueError(f'goal store: bad {what} {value!r}: use letters, digits and ._@+-')
    return value


def tag_dir(root, function, case, tag):
    return (Path(root) / STORE / check_segment(function, 'function') / check_segment(case, 'case')
            / check_segment(tag, 'tag'))


def sha256(path):
    digest = hashlib.sha256()
    with open(path, 'rb') as stream:
        for block in iter(lambda: stream.read(1 << 16), b''):
            digest.update(block)
    return digest.hexdigest()


def now_utc(now=None):
    return time.strftime('%Y-%m-%dT%H:%M:%SZ', time.gmtime(time.time() if now is None else now))


def write_manifest(directory, manifest):
    temporary = directory / ('.' + MANIFEST + '.tmp')
    temporary.write_text(json.dumps(manifest, indent=2, sort_keys=True) + '\n')
    os.replace(temporary, directory / MANIFEST)


def save(root, function, case, tag, files, *, head, bank, command, now=None):
    """Copy FILES (path, name in the store) into one tag dir and write its manifest.

    Refuses files over GOAL_MAX_BYTES and an existing tag dir with different content."""
    directory = tag_dir(root, function, case, tag)
    entries = []
    for source, name in files:
        size = os.stat(source).st_size
        if size > GOAL_MAX_BYTES:
            raise ValueError(f'goal store: {source} has {size} bytes; the store keeps files up to '
                             f'{GOAL_MAX_BYTES} bytes')
        entries.append({'name': name, 'source': os.path.abspath(source), 'bytes': size,
                        'sha256': sha256(source)})
    for entry in entries:
        target = directory / entry['name']
        if target.exists() and sha256(target) != entry['sha256']:
            raise ValueError(f'goal store: {target} exists with other content; pick another tag')
    directory.mkdir(parents=True, exist_ok=True)
    for (source, _), entry in zip(files, entries):
        target = directory / entry['name']
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(source, target)
    manifest = {'schema': 'zesu.saved-goals.v1', 'function': function, 'case': case, 'tag': tag,
                'head': head, 'bank': bank, 'command': command, 'date': now_utc(now),
                'files': entries}
    with contextlib.suppress(OSError, ValueError):
        old = json.loads((directory / MANIFEST).read_text())
        names = {entry['name'] for entry in entries}
        manifest['files'] = [e for e in old.get('files', []) if e.get('name') not in names] + entries
    write_manifest(directory, manifest)
    return directory


def item_metadata(directory):
    with contextlib.suppress(OSError, ValueError):
        value = json.loads((Path(directory) / 'ITEM.json').read_text())
        if isinstance(value, dict):
            return value
    return {}


def case_name(root, directory):
    try:
        relative = Path(directory).resolve().relative_to(Path(root).resolve())
    except ValueError:
        relative = Path(Path(directory).name)
    parts = [p for p in relative.parts if p not in ('_build', 'agents', '.worktrees')]
    return re.sub(r'[^A-Za-z0-9._@+-]', '_', '-'.join(parts) or 'run').lstrip('._-') or 'run'


def rescue(root, directory, *, reason, log=None, now=None):
    """Move the saved goals out of DIRECTORY into the store before DIRECTORY is deleted.

    Returns (store tag dir or None, moved count). Files over GOAL_MAX_BYTES stay and are logged."""
    found, large = [], []
    for path, relative, size in goal_files(directory):
        (large if size > GOAL_MAX_BYTES else found).append((path, relative, size))
    stamp = time.strftime('%Y%m%dT%H%M%SZ', time.gmtime(time.time() if now is None else now))
    for path, _, size in large:
        if log:
            log(f'{stamp}\tgoal-too-large\t{path}\t{size}')
    if not found:
        return None, 0
    item = item_metadata(directory)
    function = item.get('function') if isinstance(item.get('function'), str) else None
    if not function or not SEGMENT.match(function):
        function = RESCUED_FUNCTION
    destination = save(root, function, case_name(root, directory), 'rescued-' + stamp,
                       [(path, relative) for path, relative, _ in found],
                       head=item.get('head'), bank=item.get('bank'),
                       command=item.get('command') or reason, now=now)
    manifest = json.loads((destination / MANIFEST).read_text())
    manifest.update(rescued_from=os.path.abspath(directory), reason=reason,
                    branch=item.get('branch'))
    write_manifest(destination, manifest)
    for path, relative, size in found:
        with contextlib.suppress(OSError):
            os.unlink(path)
        if log:
            log(f'{stamp}\tgoal-saved\t{path}\t{size}\t{destination / relative}')
    return destination, len(found)


def closure_files(directory):
    """Yield (path, relative path) of the regular closure records under DIRECTORY."""
    for current, subdirectories, names in os.walk(directory):
        subdirectories[:] = sorted(d for d in subdirectories if d not in SKIP_DIRS)
        for name in sorted(names):
            if name in CLOSURE_NAMES:
                path = os.path.join(current, name)
                with contextlib.suppress(OSError):
                    if stat.S_ISREG(os.lstat(path).st_mode):
                        yield path, os.path.relpath(path, directory)


def rescue_closures(root, directory, *, reason, log=None, now=None):
    """Move the closure records out of DIRECTORY into `_build/closures/<function>/<case>/<run>/`.

    The case is the record's `case` (else its parent dir name); the run is DIRECTORY's name
    (as for saved goals) plus the record's parent dirs below it. Returns the moved count."""
    item = item_metadata(directory)
    default_function = item.get('function') if isinstance(item.get('function'), str) else None
    run = case_name(root, directory)
    stamp = time.strftime('%Y%m%dT%H%M%SZ', time.gmtime(time.time() if now is None else now))
    moved = 0
    for path, relative in list(closure_files(directory)):
        record = {}
        with contextlib.suppress(OSError, ValueError):
            value = json.loads(Path(path).read_text())
            if isinstance(value, dict):
                record = value
        parent = Path(relative).parent
        function = record.get('function') if isinstance(record.get('function'), str) else None
        function = function or default_function
        if not function or not SEGMENT.match(function):
            function = RESCUED_FUNCTION
        case = record.get('case') if isinstance(record.get('case'), str) else None
        if not case or not SEGMENT.match(case):
            case = parent.name if parent.parts and SEGMENT.match(parent.name) else 'unknown'
        sub = '-'.join(p for p in parent.parts if p != case)
        name = re.sub(r'[^A-Za-z0-9._@+-]', '_', run + ('-' + sub if sub else '')).lstrip('._-') or 'run'
        target_dir = Path(root) / CLOSURES / function / case / name
        target = target_dir / Path(relative).name
        if target.exists() and sha256(target) != sha256(path):
            target = target_dir / (stamp + '-' + Path(relative).name)
        target_dir.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(path, target)
        with contextlib.suppress(OSError):
            os.unlink(path)
        moved += 1
        if log:
            log(f'{stamp}\tclosure-saved\t{path}\t{target}\t{reason}')
    return moved


def store_bytes(root):
    total = 0
    for current, _, names in os.walk(Path(root) / STORE):
        for name in names:
            with contextlib.suppress(OSError):
                info = os.lstat(os.path.join(current, name))
                total += info.st_blocks * 512
    return total
