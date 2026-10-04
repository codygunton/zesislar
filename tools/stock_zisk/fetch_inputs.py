#!/usr/bin/env python3
"""Fetch declared stock inputs for a checkout on the documented host."""
import argparse
import json
from pathlib import Path
import shutil
import subprocess

import manifest

URLS = {
    'zesu': 'https://github.com/Consensys/zesu.git',
    'guest': 'https://github.com/Consensys/zesu-zkvm.git',
    'zisk': 'https://github.com/0xPolygonHermez/zisk.git',
}


def fetch_source(name, source):
    path = Path(source['path'])
    if not path.exists():
        path.mkdir(parents=True)
        subprocess.run(['git', 'init', str(path)], check=True)
        subprocess.run(['git', '-C', str(path), 'remote', 'add', 'origin', URLS[name]], check=True)
        subprocess.run(['git', '-C', str(path), 'fetch', '--depth=1', 'origin', source['commit']], check=True)
        subprocess.run(['git', '-C', str(path), 'checkout', '--detach', 'FETCH_HEAD'], check=True)
    actual = subprocess.check_output(['git', '-C', str(path), 'rev-parse', 'HEAD'], text=True).strip()
    manifest.require_equal(actual, source['commit'], name+' checkout')
    tree = subprocess.check_output(['git', '-C', str(path), 'rev-parse', 'HEAD^{tree}'], text=True).strip()
    manifest.require_equal(tree, source['tree'], name+' tree')
    subprocess.run(['git', '-C', str(path), 'diff', '--exit-code', 'HEAD'], check=True)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--manifest', type=Path, default=Path('build/stock-zisk/build-recipe.json'))
    parser.add_argument('--archive', type=Path, default=Path('/home/cody/zesislar-archive/stock-inputs'))
    args = parser.parse_args()
    recipe = json.loads(args.manifest.read_text())
    for name, source in recipe['sources'].items():
        fetch_source(name, source)
    record = recipe['inputs']['object']
    target = Path(record['path'])
    if not target.exists():
        archive = args.archive/(record['sha256']+'-zesu.o')
        manifest.require_equal(manifest.digest(archive), record['sha256'], 'Archived stock object')
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(archive, target)
    manifest.require_equal(manifest.digest(target), record['sha256'], 'Stock object')
    for name, record in recipe['inputs'].items():
        manifest.require_equal(manifest.digest(record['path']), record['sha256'], name)
    manifest.check_sail_inputs(recipe['inputs'])
    print('Fetched or checked all declared stock inputs. The manifest is unchanged.')


if __name__ == '__main__':
    main()
