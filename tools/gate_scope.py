#!/usr/bin/env python3
"""Run tool suites unless the latest authenticated green gate binds their bytes."""
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys


def tools_digest(workspace):
    root = Path(workspace)
    names = subprocess.check_output([
        'git', '-C', str(root), 'ls-files', '--cached', '--others',
        '--exclude-standard', '-z', '--', 'tools/'], text=True).split('\0')
    rows = []
    for name in sorted(set(filter(None, names))):
        path = root/name
        if not path.is_file() or path.is_symlink():
            return None
        rows.append((name, hashlib.sha256(path.read_bytes()).hexdigest(), path.stat().st_mode & 0o777))
    return hashlib.sha256(json.dumps(rows).encode()).hexdigest()


def tools_unchanged(ledger, digest, *, closed, guard_reader=None):
    from gate_exit_peaks import latest
    if digest is None:
        return False
    # Gates from all worktrees share the ledger. Use the newest entry for these
    # tools bytes; an invalid newest match does not fall back to an older one.
    entry = next((entry for entry in reversed(ledger.get('gate_exit_peaks', []))
                  if isinstance(entry, dict) and isinstance(entry.get('code_identity'), dict)
                  and entry['code_identity'].get('tools_tree_sha256') == digest), None)
    if entry is None:
        return False
    try:
        identity = entry['code_identity']
        target = entry['run_kind']
        from block.harness.code.entry_chain import read_bound
        request = read_bound(entry['request'])
        selected = latest(dict(ledger, gate_exit_peaks=[entry]), target,
            ['make', '--no-print-directory', '_'+target],
            request['policy']['physical_fence_bytes'], identity,
            closed=closed, guard_reader=guard_reader)
        return selected is not None
    except (AttributeError, KeyError, OSError, TypeError, ValueError):
        return False


def main():
    from correctness_gate import aggregate_closed
    from block.harness.code.admission_memory import DEFAULT_LEDGER, ledger_transaction
    workspace = Path.cwd()
    ledger = Path(os.environ.get('ZESU_CANONICAL_LEDGER', DEFAULT_LEDGER))
    digest = tools_digest(workspace)
    with ledger_transaction(ledger) as data:
        unchanged = tools_unchanged(data, digest, closed=aggregate_closed)
    if unchanged:
        print('Tool suites skipped: the latest authenticated green gate binds unchanged tools.')
        return 0
    print('Tool suites required: tools changed or authenticated green evidence is absent.', flush=True)
    command = sys.argv[1:]
    if command[:1] == ['--']:
        command = command[1:]
    if not command:
        raise ValueError('The tool-suite command is absent.')
    return subprocess.call(command)


if __name__ == '__main__':
    raise SystemExit(main())
