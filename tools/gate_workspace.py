#!/usr/bin/env python3
"""Prepare and check the pinned source checkouts before a gate starts."""

import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess


def git(path, *arguments):
    return subprocess.check_output(
        ['git', '-C', str(path), *arguments], stderr=subprocess.PIPE)


def check_source(path, record):
    if not path.is_dir():
        raise ValueError(f'The pinned source checkout is missing: {path}')
    checks = [('HEAD', record['commit']), ('HEAD^{tree}', record['tree'])]
    for revision, expected in checks:
        actual = git(path, 'rev-parse', revision).decode().strip()
        if actual != expected:
            raise ValueError(f'The pinned source differs at {path}: {revision}')
    patch = git(path, 'diff', '--binary', 'HEAD')
    staged = git(path, 'diff', '--cached', '--binary', 'HEAD')
    if patch or staged:
        raise ValueError(f'The pinned source has tracked changes: {path}')
    if hashlib.sha256(patch).hexdigest() != record['patch_sha256']:
        raise ValueError(f'The pinned source patch hash differs: {path}')


def prepare(workspace, *, source_workspace=None, check_only=False,
            recipe='build/stock-zisk/build-recipe.json'):
    workspace = Path(workspace).resolve()
    data = json.loads((workspace / recipe).read_text())
    sources = data['sources']
    if not sources:
        raise ValueError('The gate recipe has no pinned sources.')
    if source_workspace is None and not check_only:
        common = git(workspace, 'rev-parse', '--path-format=absolute',
                     '--git-common-dir').decode().strip()
        source_workspace = Path(common).parent
    seed = Path(source_workspace).resolve() if source_workspace else None
    checked = []
    pending = []
    for name, record in sorted(sources.items()):
        relative = Path(record['path'])
        if not relative.is_absolute() and '..' in relative.parts:
            raise ValueError(f'The pinned source path contains a parent step: {name}')
        path = workspace / relative
        if os.path.lexists(path):
            check_source(path, record)
        elif check_only or relative.is_absolute() or seed is None or seed == workspace:
            raise ValueError(f'The pinned source checkout is missing: {path}')
        else:
            source = seed / relative
            check_source(source, record)
            pending.append((path, source))
        checked.append({'name': name, 'path': str(path),
                        'commit': record['commit'], 'tree': record['tree']})
    # Validate all inputs before creating any link. Never replace an existing path.
    for path, source in pending:
        path.parent.mkdir(parents=True, exist_ok=True)
        path.symlink_to(os.path.relpath(source, path.parent), target_is_directory=True)
    for row in checked:
        check_source(Path(row['path']), sources[row['name']])
    return {'sources': checked, 'created_links': len(pending),
            'proof_or_Dune_execution': False}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--workspace', type=Path, default=Path.cwd())
    parser.add_argument('--source-workspace', type=Path)
    parser.add_argument('--recipe', default='build/stock-zisk/build-recipe.json')
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    try:
        result = prepare(args.workspace, source_workspace=args.source_workspace,
                         check_only=args.check, recipe=args.recipe)
    except (OSError, ValueError, KeyError, subprocess.CalledProcessError) as error:
        parser.exit(2, f'Gate workspace preparation failed: {error}\n')
    print(json.dumps(result, sort_keys=True))


if __name__ == '__main__':
    main()
