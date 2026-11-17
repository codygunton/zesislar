#!/usr/bin/env python3
"""sweep_paths.py [repo|guard|out] : paths of the decodeItem sweep, derived from the checkout holding this file.

repo  the checkout (worktree) this file lives in; its tools/ (guard, fence) are the ones the sweep uses
guard <repo>/tools/resource_guard.sh
out   result root: $SWEEP_ROOT, else <primary checkout>/_build/agents/mergeq (shared across worktrees, so
      baselines such as gc32 stay comparable)
"""
import os
import subprocess
import sys
from pathlib import Path


def repo_root(here=__file__):
    return Path(here).resolve().parents[2]


def guard(repo=None):
    return (repo or repo_root()) / 'tools' / 'resource_guard.sh'


def out_root(repo=None, environ=os.environ):
    if environ.get('SWEEP_ROOT'):
        return Path(environ['SWEEP_ROOT']).resolve()
    common = subprocess.run(['git', '-C', str(repo or repo_root()), 'rev-parse', '--path-format=absolute',
                             '--git-common-dir'], capture_output=True, text=True, check=True).stdout.strip()
    return Path(common).parent / '_build' / 'agents' / 'mergeq'


if __name__ == '__main__':
    print({'repo': repo_root, 'guard': guard, 'out': out_root}[sys.argv[1]]())
