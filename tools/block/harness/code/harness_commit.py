"""Bind the shared implementation to one clean Git commit."""
from pathlib import Path
import re
import subprocess


def git(root, *args):
    result = subprocess.run(['git', '-C', str(root), *args],
                            capture_output=True, text=True, check=True)
    return result.stdout.strip()


def pin(commit, root=None):
    root = Path(root or Path(__file__).resolve().parents[4]).resolve()
    if not isinstance(commit, str) or not re.fullmatch(r'[0-9a-f]{40}', commit):
        raise ValueError('The harness requires a full Git commit.')
    if git(root, 'rev-parse', 'HEAD') != commit:
        raise ValueError('The harness checkout has another commit.')
    paths = ['tools/block', 'tools/module_memory.py']
    if git(root, 'status', '--porcelain', '--untracked-files=all', '--', *paths):
        raise ValueError('The committed harness contains uncommitted changes.')
    tree = git(root, 'rev-parse', commit + ':tools/block/harness')
    return {'schema': 'block.shared-harness.git.v1', 'root': str(root),
            'commit': commit, 'tree': tree}


def check(value):
    expected = pin(value['commit'], value['root'])
    if value != expected:
        raise ValueError('The shared harness Git identity changed.')
    return expected
