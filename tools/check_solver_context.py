#!/usr/bin/env python3
"""Find solver calls that bypass the selected-input API in Automation2."""
import argparse
import json
from pathlib import Path
import re


def mask(text):
    """Keep offsets while removing nested comments and string literals."""
    result = list(text)
    depth = 0
    quoted = False
    i = 0
    while i < len(text):
        pair = text[i:i + 2]
        if not quoted and pair == '(*':
            depth += 1
            result[i:i + 2] = '  '
            i += 2
            continue
        if depth and pair == '*)':
            depth -= 1
            result[i:i + 2] = '  '
            i += 2
            continue
        if not depth and text[i] == '"':
            if quoted and pair == '""':
                result[i:i + 2] = '  '
                i += 2
                continue
            quoted = not quoted
            result[i] = ' '
        elif (depth or quoted) and text[i] != '\n':
            result[i] = ' '
        i += 1
    return ''.join(result)


SOLVER = re.compile(
    r'(?<![\w.])(?:(?:[\w]+\.)*Zify\.zify_[A-Za-z0-9_]+'
    r'|(?:[\w]+\.)*(?:lia|xlia|nia|xnia|zify|bv_solve|ring|ring_simplify|rc_lia))'
    r'(?!\w)(?!\.[A-Za-z_])')

WRAPPER = re.compile(
    r'(?<![\w.])(?:ZesuSsz\.Automation2\.)?'
    r'(?:SearchBudget\.zesu_solve_selected|ContextCollection\.zesu_solve_solver)'
    r'\s*(?:\([^()]*\)|[A-Za-z_][\w.]*)\s+ltac:\s*\(')



def inspect(path):
    text = path.read_text(encoding='utf-8')
    clean = mask(text)
    spans = []
    for start in WRAPPER.finditer(clean):
        depth = 1
        i = start.end()
        while i < len(clean) and depth:
            depth += (clean[i] == '(') - (clean[i] == ')')
            i += 1
        spans.append((start.end(), i - 1))
    calls = []
    for match in SOLVER.finditer(clean):
        if re.search(r'\bLtac2?(?:\s+@\s*|\s+)$', clean[:match.start()]):
            continue
        calls.append({
            'file': str(path), 'line': clean.count('\n', 0, match.start()) + 1,
            'solver': match.group(),
            'protected': any(a <= match.start() < b for a, b in spans),
        })
    forbidden = []
    for match in re.finditer(r'\bzesu_context_collection_off(?:_intro)?\b', clean):
        forbidden.append({'file': str(path),
                          'line': clean.count('\n', 0, match.start()) + 1,
                          'reason': 'Unchecked collection-off fallback'})
    return calls, forbidden


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--json', type=Path)
    args = parser.parse_args()
    root = Path(__file__).resolve().parents[1]
    calls, forbidden = [], []
    for path in sorted((root / 'ZesuSsz/Automation2').glob('*.v')):
        found, rejected = inspect(path)
        calls.extend(found)
        forbidden.extend(rejected)
    result = {'calls': calls, 'forbidden': forbidden,
              'limits': 'Source syntax only. Native backend checks cover captured library bindings.'}
    if args.json:
        args.json.write_text(json.dumps(result, indent=2) + '\n', encoding='utf-8')
    missing = [call for call in calls if not call['protected']]
    print(f'{len(calls)} calls; {len(missing)} unprotected calls; {len(forbidden)} forbidden fallbacks.')
    return bool(missing or forbidden)


if __name__ == '__main__':
    raise SystemExit(main())
