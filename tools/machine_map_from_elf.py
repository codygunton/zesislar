#!/usr/bin/env python3
"""Read ELF addresses and combine them with an explicit Sail policy record."""
import argparse
import json
import re
from pathlib import Path
from elftools.elf.elffile import ELFFile

PINNED = {'mapStartPc': '_start', 'mapReadInputPc': 'read_input',
          'mapWriteOutputPc': 'write_output', 'mapZkvmExitPc': 'zkvm_exit',
          'mapMemcpyPc': 'memcpy', 'mapMainPc': 'main',
          'mapHeapTopAddress': 'ZKVM_HEAP_TOP', 'mapHeapPosAddress': 'ZKVM_HEAP_POS',
          'mapInputBufferAddress': 'input_buffer', 'mapIoContextAddress': 'binary_fv_io_context'}


def read_elf(path):
    with Path(path).open('rb') as stream:
        elf = ELFFile(stream)
        if elf.elfclass != 64 or elf['e_machine'] != 'EM_RISCV':
            raise ValueError('The ELF must contain 64-bit RISC-V code.')
        table = elf.get_section_by_name('.symtab')
        if table is None:
            raise ValueError('The ELF must contain a symbol table.')
        symbols = {s.name: (s['st_value'], s['st_size']) for s in table.iter_symbols() if s.name}
        fields = {field: symbols[name][0] for field, name in PINNED.items()}
        for section, base, end in [('.text', 'mapTextBase', 'mapTextEnd'),
                                   ('.rodata', 'mapRodataBase', 'mapRodataEnd')]:
            sec = elf.get_section_by_name(section)
            fields[base] = sec['sh_addr']
            fields[end] = sec['sh_addr'] + sec['sh_size']
        fields.update(mapDataBase=elf.get_section_by_name('.sdata')['sh_addr'],
                      mapHeapBase=symbols['heap_buffer'][0],
                      mapHeapEnd=sum(symbols['heap_buffer']),
                      mapInputCapacity=symbols['input_buffer'][1])
        segments = [{key: seg[key] for key in ('p_vaddr', 'p_memsz', 'p_filesz', 'p_flags')}
                    for seg in elf.iter_segments() if seg['p_type'] == 'PT_LOAD']
        for name in PINNED.values():
            addr, size = symbols[name]
            if not any(s['p_vaddr'] <= addr and addr + max(1, size) <= s['p_vaddr'] + s['p_memsz']
                       for s in segments):
                raise ValueError(f'The symbol {name} lies outside a load segment.')
        return fields, symbols, segments


def read_record(path, name='defaultMap'):
    text = Path(path).read_text()
    match = re.search(r'Definition\s+' + re.escape(name) + r'\s*:.*?:=\s*\{\|(.*?)\|\}', text, re.S)
    if not match:
        raise ValueError(f'The file does not define the literal record {name}.')
    fields = {}
    for key, raw in re.findall(r'(map\w+)\s*:=\s*([^;]+)', match[1]):
        raw = raw.strip().removesuffix('%string')
        fields[key] = (raw == 'true') if raw in ('true', 'false') else (
            json.loads(raw) if raw.startswith('"') else int(raw, 0))
    return fields


def coq_literal(fields):
    def value(v):
        if isinstance(v, bool): return str(v).lower()
        if isinstance(v, str): return json.dumps(v) + '%string'
        return str(v) if v < 16 else hex(v)
    return '{|\n' + ';\n'.join(f'  {k} := {value(v)}' for k, v in fields.items()) + '\n|}.'


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('elf', type=Path)
    parser.add_argument('--policy-record', required=True, type=Path,
                        help='The Machine.v record supplies Sail flags, which an ELF does not encode.')
    parser.add_argument('--record-name', default='defaultMap')
    parser.add_argument('--format', choices=['json', 'coq'], default='json')
    parser.add_argument('--output-name', default='extractedMap', help='The emitted Coq definition name.')
    parser.add_argument('--check', action='store_true', help='Require exact equality with the policy record.')
    args = parser.parse_args()
    policy = read_record(args.policy_record, args.record_name)
    addresses, _, _ = read_elf(args.elf)
    if args.check and any(policy.get(k) != v for k, v in addresses.items()):
        parser.error('The ELF address fields differ from the supplied record.')
    policy.update(addresses)
    if args.format == 'json':
        print(json.dumps(policy, indent=2))
    else:
        if not re.fullmatch(r'[A-Za-z_][A-Za-z0-9_]*', args.output_name):
            parser.error('The output name must be a Coq identifier.')
        print('Require Import ZesuMachineMap.Machine.')
        print(f'Definition {args.output_name} : MachineMap := ' + coq_literal(policy))

if __name__ == '__main__':
    main()
