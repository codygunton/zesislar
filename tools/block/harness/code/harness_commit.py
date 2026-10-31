"""Bind each launch to one managed detached Git checkout."""
from contextlib import contextmanager
from pathlib import Path
import fcntl
import hashlib
import json
import os
import re
import subprocess
import sys


SCHEMA = 'block.shared-harness.git.v2'


def git(root, *args):
    result = subprocess.run(['git', '-C', str(root), *args],
                            capture_output=True, text=True, check=True)
    return result.stdout.strip()


def full_commit(commit):
    if not isinstance(commit, str) or not re.fullmatch(r'[0-9a-f]{40}', commit):
        raise ValueError('The harness requires a full Git commit.')
    return commit


def clean(root, *, immutable=False):
    if git(root, 'status', '--porcelain', '--untracked-files=all', '--', 'tools'):
        raise ValueError('The committed harness contains uncommitted changes.')
    if immutable and git(root, 'status', '--porcelain', '--untracked-files=no'):
        raise ValueError('The immutable launch checkout contains tracked changes.')


def repository(root):
    common = Path(git(root, 'rev-parse', '--git-common-dir'))
    return (common if common.is_absolute() else root / common).resolve().parent


def destination(root, commit):
    return repository(root) / '.worktrees' / ('shared-block-' + commit)


def validate_checkout(root, commit):
    if Path(git(root, 'rev-parse', '--show-toplevel')).resolve() != root:
        raise ValueError('The launch path is not one Git checkout root.')
    if git(root, 'rev-parse', 'HEAD') != commit:
        raise ValueError('The harness checkout has another commit.')
    detached = subprocess.run(['git', '-C', str(root), 'symbolic-ref', '-q', 'HEAD'],
                              capture_output=True, text=True)
    if detached.returncode != 1:
        raise ValueError('The launch checkout must have a detached HEAD.')
    if root != destination(root, commit) or root.is_symlink():
        raise ValueError('The launch checkout is outside its per-pin location.')
    clean(root, immutable=True)
    return {'schema': SCHEMA, 'root': str(root), 'commit': commit,
            'tree': git(root, 'rev-parse', commit + ':tools/block/harness'),
            'tools_tree': git(root, 'rev-parse', commit + ':tools')}


@contextmanager
def checkout_lock(parent):
    parent.mkdir(parents=True, exist_ok=True)
    with (parent / '.shared-block-checkouts.lock').open('a') as stream:
        fcntl.flock(stream, fcntl.LOCK_EX)
        yield


def checkout(commit, root):
    """Reuse Git objects and never change an existing per-pin checkout."""
    commit = full_commit(commit)
    root = Path(root).resolve()
    clean(root)
    if git(root, 'rev-parse', commit + '^{commit}') != commit:
        raise ValueError('The launch pin does not identify one commit.')
    target = destination(root, commit)
    with checkout_lock(target.parent):
        if target.is_symlink():
            raise ValueError('The launch checkout path is a symlink.')
        if not target.exists():
            subprocess.run(['git', '-C', str(root), 'worktree', 'add', '--detach',
                            str(target), commit], capture_output=True, text=True, check=True)
        return validate_checkout(target, commit)


def pin(commit, root=None):
    root = Path(root or Path(__file__).resolve().parents[4]).resolve()
    full_commit(commit)
    if git(root, 'rev-parse', 'HEAD') != commit:
        raise ValueError('The harness checkout has another commit.')
    clean(root)
    return checkout(commit, root)


def check(value):
    root = Path(value['root']).resolve()
    commit = full_commit(value['commit'])
    if value.get('schema') == 'block.shared-harness.git.v1':
        # Historical records keep their original validation and outcome.
        if git(root, 'rev-parse', 'HEAD') != commit:
            raise ValueError('The harness checkout has another commit.')
        clean(root)
        expected = {'schema': 'block.shared-harness.git.v1', 'root': str(root),
                    'commit': commit, 'tree': git(root, 'rev-parse', commit + ':tools/block/harness')}
    elif value.get('schema') == SCHEMA:
        expected = validate_checkout(root, commit)
    else:
        raise ValueError('The shared harness Git schema is unsupported.')
    if value != expected:
        raise ValueError('The shared harness Git identity changed.')
    return expected


def option(arguments, name):
    values = []
    for index, word in enumerate(arguments):
        if word == name:
            if index + 1 == len(arguments):
                raise ValueError('The launch pin has no value.')
            values.append(arguments[index + 1])
        elif word.startswith(name + '='):
            values.append(word.split('=', 1)[1])
    if len(values) > 1:
        raise ValueError('The launch repeats its harness pin.')
    return values[0] if values else None


def runtime_pin(path, expected):
    raw = Path(path).read_bytes()
    if hashlib.sha256(raw).hexdigest() != expected:
        raise ValueError('The launch runtime binding changed.')
    def pairs(rows):
        value = {}
        for key, item in rows:
            if key in value:
                raise ValueError('The launch runtime repeats a JSON key.')
            value[key] = item
        return value
    return json.loads(raw, object_pairs_hook=pairs)['harness']['commit']


def bootstrap(script, arguments, *, execute=os.execv):
    """Enter pinned implementation code before importing the shared backend."""
    root = Path(script).resolve().parents[3]
    selected = option(arguments, '--harness-commit')
    if arguments[:1] == ['--run']:
        if len(arguments) != 3:
            raise ValueError('The run command requires one bound runtime.')
        selected = runtime_pin(arguments[1], arguments[2])
    elif arguments[:1] == ['--refresh-memory'] and selected is None:
        if len(arguments) < 3:
            raise ValueError('The refresh command requires one bound runtime.')
        selected = runtime_pin(arguments[1], arguments[2])
    elif selected is None and any(word in {'-h', '--help'} for word in arguments):
        return
    full_commit(selected)
    if arguments[:1] not in [['--run'], ['--refresh-memory']]:
        if git(root, 'rev-parse', 'HEAD') != selected:
            raise ValueError('The harness checkout has another commit.')
    launch = checkout(selected, root)
    target = Path(launch['root']) / 'tools/block/harness/scratch.py'
    if target.resolve() != Path(script).resolve():
        execute(sys.executable, [sys.executable, '-B', str(target), *arguments])
        raise RuntimeError('The immutable launch did not replace the command.')
