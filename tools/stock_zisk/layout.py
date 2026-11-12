#!/usr/bin/env python3
"""Render every ELF-layout constant outside Machine.v from the selected ELF.

The platform adapter, its smoke cases, and the platform audit carry the
text and read-only extents of the selected ELF. A rebuilt ELF moves these
extents (2026-11-11: the compressed-free build ends .text at 0x8010f5e4,
not 0x8010fd78). This tool rewrites them from the recipe's checked ELF
layout and symbol table; `--check` fails when any of them disagrees.
`tools/stock_zisk/machine_map/generate.py` then renders Machine.v from the
same layout.
"""
import argparse
import json
from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parents[2]
BUILD = ROOT / 'build/stock-zisk'
ADAPTER = ROOT / 'tools/stock_zisk/platform/adapter.sail'
SMOKE = ROOT / 'tools/stock_zisk/platform/smoke.py'
PAIR = re.compile(r'zisk_contains\(a, w, (\d+), (\d+)\)')
CASE = re.compile(r'^ \("(?P<name>[a-z_]+)", "[a-z]+", (?P<address>0x[0-9a-f]+),', re.M)


def load_segments(recipe):
    """Return the PT_LOAD extents in the platform audit's form."""
    return [{'start': s['p_vaddr'], 'end': s['p_vaddr'] + s['p_memsz'], 'flags': s['p_flags'],
             'file_bytes': s['p_filesz']}
            for s in recipe['elf_layout']['segments'] if s['p_type'] == 'PT_LOAD']


def extents(segments):
    """Return the execute-only and read-only extents; the layout has one of each."""
    text = [s for s in segments if s['flags'] == 1]
    rodata = [s for s in segments if s['flags'] == 4]
    if len(text) != 1 or len(rodata) != 1:
        raise ValueError('The ELF must have one execute-only and one read-only load segment.')
    return (text[0]['start'], text[0]['end']), (rodata[0]['start'], rodata[0]['end'])


def symbols(table):
    result = {}
    for row in table.splitlines():
        fields = row.split()
        if len(fields) >= 8 and fields[0].endswith(':') and fields[0][:-1].isdigit():
            result[fields[7]] = int(fields[1], 16)
    return result


def render_adapter(source, text, rodata, rom):
    """Replace the two numeric ranges inside the ROM window: the lower is .text."""
    pairs = sorted({(int(a), int(b)) for a, b in PAIR.findall(source)
                    if rom[0] <= int(a) < rom[1]})
    if len(pairs) != 2:
        raise ValueError(f'The adapter must name exactly two ROM ranges, found {pairs}.')
    replacement = dict(zip(pairs, (text, rodata)))

    def substitute(match):
        pair = (int(match[1]), int(match[2]))
        new = replacement.get(pair, pair)
        return f'zisk_contains(a, w, {new[0]}, {new[1]})'
    return PAIR.sub(substitute, source)


def smoke_addresses(text, rodata, symbol):
    return {'executable_text': text[0], 'text_data_read': text[0], 'oversized_input_end': text[0],
            'read_only_data': rodata[0], 'rodata_write': rodata[0],
            'text_end_crossing': text[1] - 2, 'rodata_end_crossing': rodata[1] - 4,
            'heap': symbol['ZKVM_HEAP_POS']}


def render_smoke(source, addresses):
    seen = set()

    def substitute(match):
        name = match['name']
        if name not in addresses:
            return match[0]
        seen.add(name)
        return match[0].replace(match['address'], hex(addresses[name]))
    result = CASE.sub(substitute, source)
    if seen != set(addresses):
        raise ValueError(f'The smoke table lacks cases: {sorted(set(addresses) - seen)}')
    return result


def render(build=BUILD, adapter=ADAPTER, smoke=SMOKE):
    """Return {path: (current text, rendered text)} for every layout-bearing file."""
    recipe = json.loads((build / 'build-recipe.json').read_text())
    audit_path = build / 'platform-audit.json'
    audit = json.loads(audit_path.read_text())
    segments = load_segments(recipe)
    text, rodata = extents(segments)
    constants = audit['constants']
    rom = (constants['ROM_ADDR'], constants['ROM_ADDR'] + constants['ROM_SIZE'])
    if not (rom[0] <= text[0] < text[1] <= rodata[0] < rodata[1] <= rom[1]):
        raise ValueError('The text and read-only extents must lie in order inside the ROM window.')
    symbol = symbols((build / 'symbols.txt').read_text())
    rendered_audit = dict(audit, load_segments=segments)
    outputs = {}
    for path, new in [(audit_path, json.dumps(rendered_audit, indent=2) + '\n'),
                      (adapter, render_adapter(adapter.read_text(), text, rodata, rom)),
                      (smoke, render_smoke(smoke.read_text(), smoke_addresses(text, rodata, symbol)))]:
        outputs[path] = (path.read_text(), new)
    return outputs


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--build', type=Path, default=BUILD)
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    stale = []
    for path, (current, new) in render(args.build.resolve()).items():
        if current != new:
            stale.append(path)
            if not args.check:
                path.write_text(new)
    label = ', '.join(str(path.relative_to(ROOT)) for path in stale)
    if args.check and stale:
        sys.exit(f'ELF layout constants differ from the selected ELF: {label}')
    print(('updated ' + label) if stale else 'ELF layout constants match the selected ELF')


if __name__ == '__main__':
    main()
