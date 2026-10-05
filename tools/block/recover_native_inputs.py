#!/usr/bin/env python3
"""Recover frozen objects with atomic local replacements, preserving current bytes."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import tempfile

from archive_discovery import store


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def recover(path, archive_record, owned_root, archive):
    path = Path(path)
    owned_root = Path(owned_root).resolve()
    # Check the parent, because the final object can be a cache symlink.
    if not path.parent.resolve().is_relative_to(owned_root):
        raise ValueError('The recovery object is outside the owned build directory')
    frozen = Path(archive_record['archive_path'])
    if digest(frozen) != archive_record['sha256']:
        raise ValueError('The frozen archive hash differs')
    previous = store(archive, path.read_bytes())
    before = path.lstat()
    descriptor, temporary = tempfile.mkstemp(prefix='.frozen-object-', dir=path.parent)
    try:
        with os.fdopen(descriptor, 'wb') as output:
            output.write(frozen.read_bytes())
        os.chmod(temporary, 0o444)
        os.replace(temporary, path)
    finally:
        if os.path.exists(temporary):
            os.unlink(temporary)
    if path.is_symlink() or digest(path) != archive_record['sha256']:
        raise ValueError('The local recovery hash differs')
    return {'path': str(path), 'previous': previous, 'frozen': archive_record,
            'previous_inode': before.st_ino, 'previous_links': before.st_nlink,
            'recovered_inode': path.stat().st_ino, 'local_replacement': True}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ('baseline', 'index', 'owned-root', 'archive', 'out'):
        parser.add_argument('--' + name, required=True)
    args = parser.parse_args()
    baseline = json.loads(Path(args.baseline).read_text())
    index = json.loads(Path(args.index).read_text())
    recovered = []
    for path, expected in baseline['inputs'].items():
        if path.endswith('.vo') and digest(path) != expected:
            record = index[path]
            if record['sha256'] != expected:
                raise ValueError('The archive record differs from the frozen input')
            recovered.append(recover(path, record, args.owned_root, args.archive))
    checks = []
    for path, expected in baseline['inputs'].items():
        if Path(path).suffix in ('.v', '.vo'):
            actual = digest(path)
            if actual != expected:
                raise ValueError('A frozen native input still differs: ' + path)
            checks.append({'path': path, 'sha256': actual})
    capture = str(Path('tools/block/complete_goals_mcp.py').resolve())
    current = store(args.archive, Path(capture).read_bytes())
    report = {'root_commit': baseline['root_commit'], 'recovered_objects': recovered,
              'native_hash_checks': checks, 'capture_only_exception': {
                  'path': capture, 'measured_sha256': baseline['inputs'][capture], 'current': current,
                  'reason': 'Approved post-run None repair; no proof command changes.'},
              'rebuild_provenance': 'Unknown. Recovery restores verified frozen bytes.',
              'proof_changes': False, 'code_sha256': digest(__file__)}
    Path(args.out).write_text(json.dumps(report, indent=2)+'\n')


if __name__ == '__main__':
    main()
