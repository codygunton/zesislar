#!/usr/bin/env python3
"""The largest memory resources of rendered FP301 entries, to choose `word_binders` slots.

    python3 tools/block/entry_sizes.py [--top N] [--json] PilotXXXXEntries.v ...

For each entry definition (`Definition <name> ... : iProp Sigma := ...`) of each module, the memory
resources (`↦ₘ∗`, `↦ₘ`) at the top separating conjunction, largest first: characters, term atoms
(identifiers and literals), the address as `address_offset` reads it (base, constant) and, for a
literal byte list, its length and each aligned 8-byte group: the size of W when the group is
`bv_extract 0 8 W` … `bv_extract 56 8 W` of one W (a word slot), else `-`. A `word_binders` slot names
the base as `region` and the group's byte offset from it as `offset`."""
import argparse
import json
import re
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import entry_hist  # noqa: E402

ATOM = re.compile(r"[A-Za-z_][\w'.]*|\d+")
DEFINITION = re.compile(r"^Definition (\S+) [^\n]*?: iProp Sigma := (.*?)\.$", re.M | re.S)


def atoms(text):
    return len(ATOM.findall(text))


def top_conjuncts(body):
    """The conjuncts of `body` at the shallowest depth that has a separating conjunction."""
    depth, stars = 0, []
    for position, character in enumerate(body):
        if character in '([{':
            depth += 1
        elif character in ')]}':
            depth -= 1
        elif body.startswith(' ∗ ', position):
            stars.append((depth, position))
    if not stars:
        return [body]
    shallow = min(depth for depth, _ in stars)
    parts, start = [], 0
    for depth, position in stars:
        if depth == shallow:
            parts.append(body[start:position])
            start = position + 3
    parts.append(body[start:])
    return parts


def memory_rows(body):
    rows = []
    for part in top_conjuncts(body):
        match = re.fullmatch(r'\s*(.*?) (↦ₘ∗|↦ₘ) (.*?)\s*', part, re.S)
        if match is None:
            continue
        base, constant = entry_hist.address_offset(match[1])
        row = {'address': entry_hist.normal(match[1].replace('%Z', '')), 'base': base, 'constant': constant,
               'operator': match[2], 'chars': len(part), 'atoms': atoms(part)}
        items = entry_hist._list_items(match[3]) if match[2] == '↦ₘ∗' else None
        if items and items != ['']:
            row['bytes'] = len(items)
            row['words'] = {offset: (len(word) if (word := entry_hist._word_of_bytes(items[offset:offset + 8]))
                                     else None)
                            for offset in range(0, len(items) - 7, 8)}
        rows.append(row)
    return sorted(rows, key=lambda row: -row['chars'])


def main():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument('modules', nargs='+', type=Path)
    parser.add_argument('--top', type=int, default=5)
    parser.add_argument('--json', action='store_true')
    options = parser.parse_args()
    report = {}
    for module in options.modules:
        for name, body in DEFINITION.findall(module.read_text()):
            rows = memory_rows(body)
            if rows:
                report[name] = {'module': str(module), 'chars': len(body), 'memory': rows[:options.top]}
    if options.json:
        print(json.dumps(report, indent=1))
        return 0
    for name, entry in report.items():
        print('%s  (%d chars)' % (name, entry['chars']))
        for row in entry['memory']:
            words = ''
            if 'words' in row:
                words = '  %d bytes; words ' % row['bytes'] + ' '.join(
                    '%d:%s' % (offset, '-' if size is None else size) for offset, size in row['words'].items())
            print('  %8d chars %7d atoms  %s %s  [base %s%+d]%s' % (
                row['chars'], row['atoms'], row['address'], row['operator'], row['base'], row['constant'], words))
    return 0


if __name__ == '__main__':
    sys.exit(main())
