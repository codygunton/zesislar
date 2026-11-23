#!/usr/bin/env python3
"""Render ZesuSsz/Generated/Stock/Symbols.v from the .symtab and section table of the pinned ELF.

One parsing-only Notation per symbol listed in tools/oblig/symbols.json; its body
is the symbol's address literal typed `Z`, the form of every address constant in
`ZesuSsz/Contracts/` (AGENTS.md, Constants). Hand-written and agent-written files
name code and data through these notations, never through address literals
(tools/oblig/check_relocatable.py).

Notation names are derived from the symbol name: `sym_` followed by the symbol
with every maximal run of characters outside [A-Za-z0-9] replaced by `_` and
leading or trailing `_` removed. Two symbols that map to one name are refused.

The list's optional `sections` (section names such as `.text`) add two notations each,
read from the ELF section header table: `sec_<stem>_start` (sh_addr) and
`sec_<stem>_end` (sh_addr + sh_size, exclusive). They are the bounds that a
code-disjointness goal names (`x + n <= A \\/ B <= x`, tools/oblig/symbolize.py);
the .symtab holds no symbol at most of them.

    render_symbols.py [--list tools/oblig/symbols.json] [--elf ELF] [--output FILE] [--check]

`--check` renders in memory and fails when the output file differs.
"""
import argparse
import hashlib
import json
import re
import sys
from pathlib import Path

from elftools.elf.elffile import ELFFile

ROOT = Path(__file__).resolve().parents[2]
DEFAULT_LIST = ROOT / 'tools/oblig/symbols.json'
SCHEMA = 'zesu.symbols.v1'


class SymbolError(Exception):
    pass


def stem(name):
    text = re.sub(r'[^A-Za-z0-9]+', '_', name).strip('_')
    if not text:
        raise SymbolError(f'name {name!r} yields an empty notation name')
    return text


def notation_name(symbol):
    return 'sym_' + stem(symbol)


def section_names(section):
    """(start notation, end notation) of a section name."""
    base = 'sec_' + stem(section)
    return base + '_start', base + '_end'


def load_list(path):
    data = json.loads(Path(path).read_text())
    if data.get('schema') != SCHEMA:
        raise SymbolError(f'{path}: schema must be {SCHEMA}')
    symbols = data.get('symbols')
    if not isinstance(symbols, list) or not all(isinstance(s, str) and s for s in symbols):
        raise SymbolError(f'{path}: symbols must be a list of non-empty strings')
    if len(set(symbols)) != len(symbols):
        raise SymbolError(f'{path}: duplicate symbol')
    sections = data.setdefault('sections', [])
    if not isinstance(sections, list) or not all(isinstance(s, str) and s for s in sections):
        raise SymbolError(f'{path}: sections must be a list of non-empty strings')
    if len(set(sections)) != len(sections):
        raise SymbolError(f'{path}: duplicate section')
    return data


def symbol_addresses(elf_path, wanted):
    """Return {symbol: address}; each wanted symbol must have exactly one defined entry."""
    wanted = set(wanted)
    found = {name: [] for name in wanted}
    with open(elf_path, 'rb') as handle:
        table = ELFFile(handle).get_section_by_name('.symtab')
        if table is None:
            raise SymbolError(f'{elf_path}: no .symtab')
        for symbol in table.iter_symbols():
            if symbol.name in found and symbol['st_shndx'] != 'SHN_UNDEF':
                found[symbol.name].append(symbol['st_value'])
    for name in sorted(wanted):
        if len(found[name]) != 1:
            raise SymbolError(f'{elf_path}: symbol {name!r} has {len(found[name])} defined entries, need 1')
    return {name: rows[0] for name, rows in found.items()}


def section_bounds(elf_path, wanted):
    """Return {section: (start, exclusive end)}; each wanted section must exist and be allocated."""
    out = {}
    with open(elf_path, 'rb') as handle:
        elf = ELFFile(handle)
        for name in wanted:
            section = elf.get_section_by_name(name)
            if section is None or not section['sh_addr']:
                raise SymbolError(f'{elf_path}: no allocated section {name!r}')
            out[name] = (section['sh_addr'], section['sh_addr'] + section['sh_size'])
    return out


def render(symbols, addresses, elf_label, elf_sha256, list_label, sections=(), bounds=None):
    names = {}
    for symbol in symbols:
        if any(token in symbol for token in ('(*', '*)', '"')):
            raise SymbolError(f'symbol {symbol!r} cannot be quoted in a Rocq comment')
        name = notation_name(symbol)
        if name in names:
            raise SymbolError(f'symbols {names[name]!r} and {symbol!r} both map to {name}')
        names[name] = symbol
    bounds = bounds or {}
    section_rows = []
    for section in sections:
        if any(token in section for token in ('(*', '*)', '"')):
            raise SymbolError(f'section {section!r} cannot be quoted in a Rocq comment')
        for name, value, edge in zip(section_names(section), bounds[section], ('start', 'end')):
            if name in names:
                raise SymbolError(f'{names[name]!r} and section {section!r} both map to {name}')
            names[name] = section
            section_rows.append((name, section, edge, value))
    lines = [
        '(* Generated by tools/oblig/render_symbols.py from ' + list_label + '. Do not edit. *)',
        '(* ELF: ' + elf_label + ' sha256 ' + elf_sha256 + ' *)',
        '(* Notation <- symbol: *)',
    ]
    lines += [f'(*   {notation_name(symbol)} <- "{symbol}" *)' for symbol in symbols]
    if section_rows:
        lines.append('(* Notation <- section bound (exclusive end): *)')
        lines += [f'(*   {name} <- {edge} of "{section}" *)' for name, section, edge, _ in section_rows]
    lines += ['', 'From Coq Require Import ZArith.', '']
    lines += [f'Notation {notation_name(symbol)} := (({addresses[symbol]:#x}) : Z) (only parsing).'
              for symbol in symbols]
    lines += [f'Notation {name} := (({value:#x}) : Z) (only parsing).' for name, _, _, value in section_rows]
    return '\n'.join(lines) + '\n'


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__.split('\n', 1)[0])
    parser.add_argument('--list', default=str(DEFAULT_LIST))
    parser.add_argument('--elf')
    parser.add_argument('--output')
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args(argv)
    try:
        data = load_list(args.list)
        elf = Path(args.elf or ROOT / data['elf'])
        output = Path(args.output or ROOT / data['output'])
        addresses = symbol_addresses(elf, data['symbols'])
        bounds = section_bounds(elf, data['sections'])
        label = elf.resolve().relative_to(ROOT) if elf.resolve().is_relative_to(ROOT) else elf.name
        list_label = Path(args.list).resolve()
        list_label = list_label.relative_to(ROOT) if list_label.is_relative_to(ROOT) else list_label.name
        text = render(data['symbols'], addresses, str(label),
                      hashlib.sha256(elf.read_bytes()).hexdigest(), str(list_label), data['sections'], bounds)
    except (SymbolError, OSError, KeyError, json.JSONDecodeError) as error:
        print(f'render_symbols: {error}', file=sys.stderr)
        return 2
    count = len(data['symbols']) + 2 * len(data['sections'])
    if args.check:
        if not output.is_file() or output.read_text() != text:
            print(f'render_symbols: {output} is stale; run tools/oblig/render_symbols.py', file=sys.stderr)
            return 1
        print(f'render_symbols: {output} is current ({count} notations)')
        return 0
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(text)
    print(f'render_symbols: wrote {output} ({count} notations)')
    return 0


if __name__ == '__main__':
    sys.exit(main())
