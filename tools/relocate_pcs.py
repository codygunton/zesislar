#!/usr/bin/env python3
"""Report or apply ELF address changes. The default operation never writes files."""
import argparse
import fnmatch
from collections import Counter
import json
from pathlib import Path
import re
import shutil
import subprocess
from machine_map_from_elf import read_elf

LITERAL = re.compile(r'(?<![\w])(?:0x[0-9a-fA-F]+|[0-9]{5,})(?![\w])')
INSTRUCTION = re.compile(r'\b(?:instr|instr_pre|instr_body)\s+\(?\s*(0x[0-9a-fA-F]+|[0-9]+)')


def instruction_addresses(elf, objdump):
    output = subprocess.check_output([objdump, '-d', str(elf)], text=True)
    return {int(m.group(1), 16) for m in re.finditer(r'^\s*([0-9a-fA-F]+):\s+[0-9a-fA-F]{8}\s', output, re.M)}


def address_changes(old, new):
    old_fields, old_symbols, _ = read_elf(old)
    new_fields, new_symbols, _ = read_elf(new)
    delta = new_fields['mapMainPc'] - old_fields['mapMainPc']
    exact = {}
    for name, (address, size) in old_symbols.items():
        if name not in new_symbols or not address:
            continue
        target = new_symbols[name][0]
        if target == address:
            continue
        if address in exact and exact[address] != target:
            raise ValueError(f'The ELF aliases at {address:#x} relocate to different addresses.')
        exact[address] = target
        if name == 'binary_fv_io_context':
            for offset in (8, 16, 24, 32): exact[address + offset] = target + offset
    # End pointers also occur in bounds. Their symbols can have zero size.
    exact[old_fields['mapHeapEnd']] = new_fields['mapHeapEnd']
    exact[old_fields['mapTextEnd']] = new_fields['mapTextEnd']
    exact[old_fields['mapRodataEnd']] = new_fields['mapRodataEnd']
    def relocate(value):
        if value in exact: return exact[value]
        # _start changed size. Other text retained its instruction positions.
        if old_fields['mapReadInputPc'] <= value < old_fields['mapTextEnd']:
            return value + delta
        return value
    return relocate, delta


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--old-elf', required=True, type=Path)
    parser.add_argument('--new-elf', required=True, type=Path)
    parser.add_argument('--root', default=Path('.'), type=Path)
    parser.add_argument('--objdump', default=shutil.which('riscv64-unknown-linux-gnu-objdump') or 'objdump')
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument('--dry-run', action='store_true')
    mode.add_argument('--apply', action='store_true')
    parser.add_argument('--check', action='store_true', help='Check the proposed instruction addresses before any write.')
    parser.add_argument('--summary-json', type=Path)
    parser.add_argument('--exclude', action='append', default=[], help='Explicit relative paths or glob patterns to omit after review.')
    args = parser.parse_args()
    relocate, delta = address_changes(args.old_elf, args.new_elf)
    valid = instruction_addresses(args.new_elf, args.objdump) if args.check else set()
    counts = Counter()
    updates = []
    errors = []
    root = args.root.resolve()
    for file in sorted(root.rglob('*')):
        relative = file.relative_to(root)
        if any(fnmatch.fnmatch(str(relative), pattern) for pattern in args.exclude): continue
        if any(part.startswith('.') or part in ('_build', 'build', 'deps') for part in relative.parts): continue
        if not file.is_file() or not (file.suffix in ('.v', '.dump') or 'coverage' in file.name): continue
        try: original = file.read_text()
        except UnicodeDecodeError: continue
        lines = []
        for line_number, line in enumerate(original.splitlines(keepends=True), 1):
            def rewrite(match):
                token = match.group()
                value = int(token, 16) if token.startswith('0x') else int(token)
                changed = relocate(value)
                if changed == value: return token
                replacement = hex(changed) if token.startswith('0x') else str(changed)
                print(f'{relative}:{line_number}: {token} -> {replacement}')
                counts[str(relative.parent)] += 1
                return replacement
            # Objdump dumps use bare hexadecimal addresses before the colon.
            dump_pc = re.match(r'^(\s*)([0-9a-fA-F]+)(:)', line) if file.suffix == '.dump' else None
            if dump_pc:
                old_pc = int(dump_pc.group(2), 16)
                new_pc = relocate(old_pc)
                if new_pc != old_pc:
                    print(f'{relative}:{line_number}: {dump_pc.group(2)} -> {new_pc:x}')
                    counts[str(relative.parent)] += 1
                    line = line[:dump_pc.start(2)] + f'{new_pc:x}' + line[dump_pc.end(2):]
            updated = LITERAL.sub(rewrite, line)
            if args.check:
                for match in INSTRUCTION.finditer(updated):
                    value = int(match.group(1), 0) if match.group(1).startswith('0x') else int(match.group(1))
                    if value not in valid: errors.append(f'{relative}:{line_number}: {value:#x} is not an instruction')
            lines.append(updated)
        result = ''.join(lines)
        if result != original: updates.append((file, result))
    summary = {'text_delta': delta, 'rewrites': sum(counts.values()), 'directories': dict(counts),
               'files': len(updates), 'check_errors': errors}
    if args.summary_json: args.summary_json.write_text(json.dumps(summary, indent=2) + '\n')
    print(json.dumps(summary))
    if errors: parser.exit(1, '\n'.join(errors) + '\n')
    if args.apply:
        if not args.check: parser.error('--apply requires --check.')
        for file, result in updates: file.write_text(result)

if __name__ == '__main__':
    main()
