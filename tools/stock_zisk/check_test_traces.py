#!/usr/bin/env python3
"""Fail when a retained test-trace fixture no longer matches the selected ELF.

`ZesuSsz/Generated/TestTraces/metadata.json` binds each fixture trace to an
instruction address, its opcode, the ELF, the platform snapshot and the Isla
configuration. A rebuilt ELF can move another instruction to a fixture's
address (the compressed-free build puts 0x02008013 at the 0x800f163c load
fixture) and a new platform snapshot changes every memory trace. Such a
fixture needs a new address or new traces before proofs may consume it.
"""
import argparse
import hashlib
import json
from pathlib import Path
import sys

from elftools.elf.elffile import ELFFile

ROOT = Path(__file__).resolve().parents[2]
FIXTURES = ROOT / 'ZesuSsz/Generated/TestTraces'


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def word_at(elf, address):
    """Return the little-endian word an executable section holds at address, or None."""
    for section in elf.iter_sections():
        start = section['sh_addr']
        if section['sh_flags'] & 4 and start <= address and address + 4 <= start + section['sh_size']:
            return int.from_bytes(section.data()[address - start:address - start + 4], 'little')
    return None


def problems(fixtures=FIXTURES, build=ROOT / 'build/stock-zisk', root=ROOT):
    metadata = json.loads((fixtures / 'metadata.json').read_text())
    elf = build / 'zesu-zisk.elf'
    expected = {'elf_sha256': digest(elf),
                'snapshot_sha256': digest(build / 'platform/riscv64-zisk.ir'),
                'config_sha256': digest(root / 'ZesuSsz/riscv64_zesu.toml')}
    found = [f'metadata {key} {metadata.get(key)} differs from the current input {value}'
             for key, value in expected.items() if metadata.get(key) != value]
    with elf.open('rb') as stream:
        image = ELFFile(stream)
        for fixture in metadata['fixtures']:
            name, address = fixture['module'], fixture['address']
            word = word_at(image, address)
            if word is None or f'{word:08x}' != fixture['opcode']:
                actual = 'no code' if word is None else f'{word:08x}'
                found.append(f'{name}: {address:#x} holds {actual}, not the fixture opcode {fixture["opcode"]}')
            for suffix, key in (('.isla', 'isla_sha256'), ('.v', 'rocq_sha256')):
                if digest(fixtures / (name + suffix)) != fixture[key]:
                    found.append(f'{name}{suffix} differs from its recorded hash')
    return found


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.parse_args()
    found = problems()
    if found:
        sys.exit('Test-trace fixtures differ from the selected ELF:\n  ' + '\n  '.join(found))
    print('Test-trace fixtures match the selected ELF, platform snapshot and configuration')


if __name__ == '__main__':
    main()
