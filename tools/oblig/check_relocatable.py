#!/usr/bin/env python3
"""Refuse absolute code and data addresses in hand-written and agent-written files.

A file listed in tools/oblig/relocatable_files.json names code and data by symbol
and offset (the notations of ZesuSsz/Generated/Stock/Symbols.v, or `+0xOFFSET`
from a symbol), never by an absolute address of the pinned binary. The checker
fails on an address of the linked image (the 16 MiB above 2^31) standing as its
own token: a hexadecimal literal `0x80` followed by six hex digits, or a decimal
literal of ten digits starting `2147` then 4-9, `2148`, `2149`, `215` or `216`
then 0-4 (a little below 2^31 too). Absolute addresses belong in generated files
only.

    check_relocatable.py [--list tools/oblig/relocatable_files.json] [--root DIR] [FILE...]

With FILE arguments it checks those files instead of the list. Other tools import
`address_hits(text)` to apply the same patterns (package.py does for goal.v).

Non-address constants. A function profile (tools/block/functions/<F>.json) may list contract
constants whose values fall in the image range but are no code address, `non_address_constants`
[{`name`, `value`, `source`}]: `source` must declare `Notation <name> := ((<expr>) : Z)` with <expr>
(integers, `+ - * ^`, parentheses) equal to `value` (an integer). A literal of that value is then
no address in the residual modules of F (ZesuSsz/Residuals/<F>/) and in F's packaged goals
(package.py); any other image literal still is.
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
    re.compile(r'(?<![0-9A-Za-z_])0[xX]80[0-9a-fA-F]{6}(?![0-9a-fA-F])'),
    re.compile(r'(?<![0-9A-Za-z_])(?:2147[4-9][0-9]{5}|214[89][0-9]{6}|215[0-9]{7}|216[0-4][0-9]{6})(?![0-9])'),
)
NOTATION = r'^Notation\s+%s\s*:=\s*\(\((?P<expr>[^()]*(?:\([^()]*\)[^()]*)*)\)\s*:\s*Z\)'


def literal_value(literal):
    return int(literal, 16) if literal.lower().startswith('0x') else int(literal)


def _evaluate(expr):
    """The integer value of a Coq Z expression of integers, `+ - * ^` and parentheses, else None."""
    import ast
    import operator
    ops = {ast.Add: operator.add, ast.Sub: operator.sub, ast.Mult: operator.mul, ast.Pow: operator.pow}

    def value(node):
        if isinstance(node, ast.Constant) and type(node.value) is int:
            return node.value
        if isinstance(node, ast.UnaryOp) and isinstance(node.op, ast.USub):
            return -value(node.operand)
        if isinstance(node, ast.BinOp) and type(node.op) in ops:
            return ops[type(node.op)](value(node.left), value(node.right))
        raise ValueError(ast.dump(node))
    try:
        return value(ast.parse(expr.replace('^', '**'), mode='eval').body)
    except (SyntaxError, ValueError):
        return None


def non_address_values(function, root=ROOT):
    """The values of the profile's `non_address_constants` (module text); refused (ValueError) unless
    each row's source declares the constant with that value."""
    path = Path(root) / 'tools/block/functions' / (function + '.json')
    if not path.is_file():
        return frozenset()
    rows = json.loads(path.read_text()).get('non_address_constants', [])
    values = set()
    for row in rows:
        if set(row) != {'name', 'value', 'source'} or not isinstance(row['value'], int):
            raise ValueError(f'{path}: a non_address_constants row is {{name, value (integer), source}}')
        text = (Path(root) / row['source']).read_text()
        found = re.search(NOTATION % re.escape(row['name']), text, re.M)
        if found is None or _evaluate(found['expr']) != row['value']:
            raise ValueError(f"{path}: {row['source']} does not declare {row['name']} as {row['value']}")
        values.add(row['value'])
    return frozenset(values)


def residual_function(relative):
    """F of a residual module path ZesuSsz/Residuals/<F>/..., else None."""
    parts = Path(relative).parts
    return parts[2] if len(parts) > 3 and parts[:2] == ('ZesuSsz', 'Residuals') else None


def address_hits(text, exempt=frozenset()):
    """Return [(line number, literal)] for every absolute address literal in text whose value is not
    in `exempt` (non_address_values)."""
    hits = []
    for number, line in enumerate(text.splitlines(), 1):
        for pattern in PATTERNS:
            hits.extend((number, match.group(0)) for match in pattern.finditer(line)
                        if literal_value(match.group(0)) not in exempt)
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
    failures, exempt = 0, {}
    for name in files:
        path = Path(name) if Path(name).is_absolute() else root / name
        try:
            text = path.read_text(errors='replace')
            relative = path.resolve().relative_to(root).as_posix() if path.resolve().is_relative_to(root) else name
            function = residual_function(relative)
            if function is not None and function not in exempt:
                exempt[function] = non_address_values(function, root)
        except (OSError, ValueError) as error:
            print(f'check_relocatable: {name}: {error}', file=sys.stderr)
            return 2
        for number, literal in address_hits(text, exempt.get(function, frozenset())):
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
