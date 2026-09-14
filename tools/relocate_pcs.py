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
OFFSET = re.compile(r'\bmachinePc\s+(0x[0-9a-fA-F]+|[0-9]+)')
INSTRUCTION_OFFSET = re.compile(r'\b(?:instr|instr_pre|instr_body)\s+\(?\s*machinePc\s+(0x[0-9a-fA-F]+|[0-9]+)')
INSTRUCTION = re.compile(r'\b(?:instr|instr_pre|instr_body)\s+\(?\s*(0x[0-9a-fA-F]+|[0-9]+)')


def instruction_addresses(elf, objdump):
    output = subprocess.check_output([objdump, '-d', str(elf)], text=True)
    return {int(m.group(1), 16) for m in re.finditer(r'^\s*([0-9a-fA-F]+):\s+[0-9a-fA-F]{8}\s', output, re.M)}


def address_changes(old, new):
    old_fields, old_symbols, _ = read_elf(old)
    new_fields, new_symbols, _ = read_elf(new)
    delta = new_fields['mapMainPc'] - old_fields['mapMainPc']
    start_growth = new_symbols['_start'][1] - old_symbols['_start'][1]
    if start_growth not in (0, 8):
        raise ValueError('The start file must retain its size or insert the approved stack pair.')
    exact = {}
    for name, (address, size) in old_symbols.items():
        if name not in new_symbols or not address:
            continue
        target = new_symbols[name][0]
        if old_fields['mapReadInputPc'] <= address < old_fields['mapTextEnd'] and target != address + delta:
            raise ValueError(f'The text symbol {name} violates the common relocation delta.')
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
        # The approved start file inserts two stack instructions after the gp pair.
        if old_fields['mapStartPc'] <= value < old_fields['mapReadInputPc']:
            offset = value - old_fields['mapStartPc']
            return new_fields['mapStartPc'] + offset + (start_growth if offset >= 8 else 0)
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
    old_fields, _, _ = read_elf(args.old_elf)
    new_fields, _, _ = read_elf(args.new_elf)
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
        word_table = False
        word_scalar = False
        pending_tuple_value = False
        for line_number, line in enumerate(original.splitlines(keepends=True), 1):
            declaration = re.match(r'\s*Definition\s+(\w+)', line)
            if declaration:
                word_table = declaration.group(1).endswith('Words')
                word_scalar = bool(re.search(r'WordAt[0-9a-fA-F]+$', declaration.group(1)))
                pending_tuple_value = False
            protected = {}
            def protect(match):
                token = f'__ENCODED_WORD_{len(protected)}__'
                protected[token] = match.group()
                return token
            if word_table:
                if pending_tuple_value:
                    value = re.match(r'\s*(?:0x[0-9a-fA-F]+|[0-9]+)\b', line)
                    if value:
                        line = protect(value) + line[value.end():]
                        pending_tuple_value = False
                line = re.sub(r'(?<=,)\s*(?:0x[0-9a-fA-F]+|[0-9]+)\b', protect, line)
                if re.search(r',\s*$', line):
                    pending_tuple_value = True
            if word_scalar:
                prefix, separator, value = line.partition(':=') if declaration else ('', '', line)
                line = prefix + separator + re.sub(r'0x[0-9a-fA-F]+\b|(?<![\w])[0-9]+(?![\w])', protect, value)
            if (word_table or word_scalar) and re.search(r'\.\s*(?:\(\*.*\*\)\s*)?$', line):
                word_table = word_scalar = pending_tuple_value = False
            def rewrite(match):
                token = match.group()
                value = int(token, 16) if token.startswith('0x') else int(token)
                changed = relocate(value)
                if changed == value: return token
                replacement = hex(changed) if token.startswith('0x') else str(changed)
                print(f'{relative}:{line_number}: {token} -> {replacement}')
                counts[str(relative.parent)] += 1
                return replacement
            def rewrite_offset(match):
                token = match.group(1)
                offset = int(token, 16) if token.startswith('0x') else int(token)
                address = old_fields['mapTextBase'] + offset
                changed = relocate(address) - new_fields['mapTextBase']
                if changed == offset: return match.group()
                replacement = hex(changed) if token.startswith('0x') else str(changed)
                print(f'{relative}:{line_number}: machinePc {token} -> machinePc {replacement}')
                counts[str(relative.parent)] += 1
                return 'machinePc ' + replacement
            line = OFFSET.sub(rewrite_offset, line)
            dump = re.match(r'^(\s*)([0-9a-fA-F]+)(:\s+)([0-9a-fA-F]{8})(\s+)(.*)', line) if file.suffix == '.dump' else None
            if dump:
                # The encoded machine word is evidence, not an address literal.
                old_pc = int(dump.group(2), 16)
                new_pc = relocate(old_pc)
                pc_token = dump.group(2)
                if new_pc != old_pc:
                    pc_token = f'{new_pc:x}'
                    print(f'{relative}:{line_number}: {dump.group(2)} -> {pc_token}')
                    counts[str(relative.parent)] += 1
                def bare_target(match):
                    value = int(match.group(1), 16)
                    changed = relocate(value)
                    if changed == value: return match.group()
                    print(f'{relative}:{line_number}: {match.group(1)} -> {changed:x}')
                    counts[str(relative.parent)] += 1
                    return f'{changed:x}' + match.group(2)
                operands = re.sub(r'\b([0-9a-fA-F]+)(\s+<)', bare_target, dump.group(6))
                operands = LITERAL.sub(rewrite, operands)
                updated = dump.group(1) + pc_token + dump.group(3) + dump.group(4) + dump.group(5) + operands
                if line.endswith('\n'): updated += '\n'
            else:
                updated = LITERAL.sub(rewrite, line)
            if args.check:
                for match in INSTRUCTION_OFFSET.finditer(updated):
                    value = int(match.group(1), 0) if match.group(1).startswith('0x') else int(match.group(1))
                    address = new_fields['mapTextBase'] + value
                    if address not in valid: errors.append(f'{relative}:{line_number}: machinePc {value:#x} is not an instruction')
                for match in INSTRUCTION.finditer(updated):
                    value = int(match.group(1), 0) if match.group(1).startswith('0x') else int(match.group(1))
                    if value not in valid: errors.append(f'{relative}:{line_number}: {value:#x} is not an instruction')
            for token, encoded in protected.items(): updated = updated.replace(token, encoded)
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
