#!/usr/bin/env python3
"""Refuse absolute code and data addresses in hand-written and agent-written files.

A file listed in tools/oblig/relocatable_files.json names code and data by symbol
and offset (the notations of ZesuSsz/Generated/Stock/Symbols.v, or `+0xOFFSET`
from a symbol), never by an absolute address of the pinned binary. The checker
fails on a hexadecimal literal `0x800` followed by five hex digits, or a decimal
literal of the form `2148` followed by six digits or `21474` followed by five,
each standing as its own token. Absolute addresses belong in generated files only.

    check_relocatable.py [--list tools/oblig/relocatable_files.json] [--root DIR] [FILE...]

With FILE arguments it checks those files instead of the list. Other tools import
`address_hits(text)` to apply the same patterns (package.py does for goal.v).
"""
import argparse
from fnmatch import fnmatchcase
import json
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
DEFAULT_LIST = ROOT / 'tools/oblig/relocatable_files.json'
SCHEMA = 'zesu.relocatable-files.v1'

# A literal counts only as a whole token: no letter, digit or `_` before it and no
# digit (or, for hexadecimal, hex digit) after it, so hashes and longer numbers pass.
PATTERNS = (
    re.compile(r'(?<![0-9A-Za-z_])0[xX]800[0-9a-fA-F]{5}(?![0-9a-fA-F])'),
    re.compile(r'(?<![0-9A-Za-z_])2148[0-9]{6}(?![0-9])'),
    re.compile(r'(?<![0-9A-Za-z_])21474[0-9]{5}(?![0-9])'),
)


def address_hits(text):
    """Return [(line number, literal)] for every absolute address literal in text."""
    hits = []
    for number, line in enumerate(text.splitlines(), 1):
        for pattern in PATTERNS:
            hits.extend((number, match.group(0)) for match in pattern.finditer(line))
    return sorted(set(hits))


def listed_files(list_path, root):
    data = json.loads(Path(list_path).read_text())
    if data.get('schema') != SCHEMA:
        raise ValueError(f'{list_path}: schema must be {SCHEMA}')
    excludes = data.get('exclude', [])
    files = set()
    for pattern in data['files']:
        for path in root.glob(pattern):
            relative = path.relative_to(root).as_posix()
            if path.is_file() and not any(fnmatchcase(relative, ex) for ex in excludes):
                files.add(relative)
    return sorted(files)


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__.split('\n', 1)[0])
    parser.add_argument('--list', default=str(DEFAULT_LIST))
    parser.add_argument('--root', default=str(ROOT))
    parser.add_argument('files', nargs='*')
    args = parser.parse_args(argv)
    root = Path(args.root).resolve()
    try:
        files = args.files or listed_files(args.list, root)
    except (OSError, KeyError, ValueError) as error:
        print(f'check_relocatable: {error}', file=sys.stderr)
        return 2
    failures = 0
    for name in files:
        path = Path(name) if Path(name).is_absolute() else root / name
        try:
            text = path.read_text(errors='replace')
        except OSError as error:
            print(f'check_relocatable: {name}: {error}', file=sys.stderr)
            return 2
        for number, literal in address_hits(text):
            failures += 1
            print(f'{name}:{number}: absolute address {literal}; name it by symbol and offset '
                  '(ZesuSsz/Generated/Stock/Symbols.v)', file=sys.stderr)
    if failures:
        print(f'check_relocatable: {failures} absolute address(es) in {len(files)} checked file(s)',
              file=sys.stderr)
        return 1
    print(f'check_relocatable: {len(files)} file(s) free of absolute addresses')
    return 0


if __name__ == '__main__':
    sys.exit(main())
