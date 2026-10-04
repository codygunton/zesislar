#!/usr/bin/env python3
"""Record selected arithmetic sites from ELF bytes and relocated object DWARF."""
import argparse
import hashlib
import json
from pathlib import Path
import sys
import subprocess

from elftools.elf.elffile import ELFFile

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from dwarf import code_dwarf
from riscv import decode

SITES = [
    ('I1-long-string', 'src/stateless/mpt/rlp.zig', 52,
     [(0x800d6a38, 0x00e68733), (0x800d6a3c, 0x0ae66263)],
     'RV64 ADD computes (length + header_size) modulo 2^64. BLTU compares input_size with this unsigned result.'),
    ('I1-long-list', 'src/stateless/mpt/rlp.zig', 67,
     [(0x800d6ad8, 0x00e68733), (0x800d6adc, 0x02e67663)],
     'RV64 ADD computes (payload_length + header_size) modulo 2^64. BGEU takes the success branch when input_size is at least this unsigned result.'),
    ('I2-legacy-v-cast', 'src/stateless/rlp_decode.zig', 345,
     [(0x80002ab4, 0xfddd0813), (0x80002acc, 0x01a838b3),
      (0x80002ad0, 0x011b88b3), (0x80002ad4, 0x00185293),
      (0x80002adc, 0xfff88893), (0x80002ae0, 0x03f89893),
      (0x80002ae4, 0x0112ed33), (0x80002e38, 0x0ba83023)],
     'The subtraction uses the low two limbs of v_raw. SRLI, SLLI, and OR retain the low 64 bits of (v_raw - 35) / 2. SD stores these bits at result offset 160. This sequence has no check of discarded bits.'),
]


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def instruction(elf, pc, expected):
    section = next((s for s in elf.iter_sections()
                    if s['sh_flags'] & 4 and s['sh_addr'] <= pc < s['sh_addr'] + s['sh_size']), None)
    if section is None:
        raise ValueError(f'The site is outside executable sections: {pc:#x}')
    offset = pc - section['sh_addr']
    raw = section.data()[offset:offset + 4]
    word = int.from_bytes(raw, 'little')
    if word != expected:
        raise ValueError(f'The instruction changed at {pc:#x}: {word:08x}')
    return {'pc': hex(pc), 'word': f'{word:08x}', 'bytes_little_endian': raw.hex(),
            'decoded': decode(pc, raw)}


def source_rows(dwarf):
    result = []
    for unit in dwarf.iter_CUs():
        program = dwarf.line_program_for_CU(unit)
        if program is None:
            continue
        files = program['file_entry']
        prior = None
        for entry in program.get_entries():
            state = entry.state
            if state is None:
                continue
            if prior and state.address > prior['start']:
                result.append(dict(prior, end=state.address))
            prior = None if state.end_sequence else {
                'start': state.address, 'file': files[state.file - 1].name.decode(),
                'line': state.line, 'column': state.column}
    return result


def collect(manifest_path, out):
    recipe = json.loads(manifest_path.read_text())
    elf_path = manifest_path.parent / 'zesu-zisk.elf'
    object_path = Path(recipe['inputs']['object']['path'])
    source_root = Path(recipe['sources']['zesu']['path'])
    source_commit = subprocess.check_output(
        ['git', '-C', str(source_root), 'rev-parse', 'HEAD'], text=True).strip()
    if source_commit != recipe['sources']['zesu']['commit']:
        raise ValueError('The source commit differs from the manifest.')
    subprocess.run(['git', '-C', str(source_root), 'diff', '--quiet'], check=True)
    subprocess.run(['git', '-C', str(source_root), 'diff', '--cached', '--quiet'], check=True)
    if digest(elf_path) != recipe['elf_sha256']:
        raise ValueError('The ELF hash differs from the manifest.')
    if digest(object_path) != recipe['inputs']['object']['sha256']:
        raise ValueError('The object hash differs from the manifest.')
    with object_path.open('rb') as obj, elf_path.open('rb') as final:
        elf = ELFFile(final)
        dwarf, relocation = code_dwarf(ELFFile(obj), elf)
        lines = source_rows(dwarf)
        sites = []
        for name, source, line, words, arithmetic in SITES:
            records = [instruction(elf, pc, word) for pc, word in words]
            for record in records:
                pc = int(record['pc'], 0)
                record['dwarf_source'] = [row for row in lines if row['start'] <= pc < row['end']]
            if not any(row['file'] == Path(source).name and row['line'] == line
                       for row in records[0]['dwarf_source']):
                raise ValueError(f'The source mapping changed for {name}')
            sites.append({'name': name, 'source': source, 'source_line': line,
                          'source_sha256': digest(source_root / source),
                          'source_text': (source_root / source).read_text().splitlines()[line - 1].strip(),
                          'arithmetic_class': arithmetic, 'instructions': records})
    report = {'schema': 1, 'artifact_identity': recipe['artifact_identity'],
              'elf_sha256': digest(elf_path), 'object_sha256': digest(object_path),
              'classification': 'Static analysis. No selected-ELF execution claim.',
              'dwarf_relocation': relocation, 'sites': sites,
              'limits': ['The selected long-list comparison uses BGEU, not BLTU.',
                         'The selected long-list addition occurs at source line 67, not review line 64.',
                         'The selected narrowing cast occurs at source line 345, not review line 340.',
                         'The retained arithmetic sequence does not prove a complete decoder path.']}
    out.mkdir(parents=True, exist_ok=True)
    output = out / 'sites.json'
    output.write_text(json.dumps(report, indent=2) + '\n')
    fragment = {'artifact_identity': recipe['artifact_identity'],
                'inputs': {'static-sites/collect.py': {'path': str(Path(recipe['inputs']['generator/closure.py']['path']).parent / 'static_sites/collect.py'),
                                                        'sha256': digest(Path(__file__))}},
                'derived': {'static-sites/sites.json': {'sha256': digest(output),
                           'artifact_identity': recipe['artifact_identity'], 'schema_version': 1}}}
    canonical = Path(recipe['inputs']['generator/closure.py']['path']).parent
    for name in ('test_collect.py',):
        path = Path(__file__).with_name(name)
        fragment['inputs']['static-sites/' + name] = {
            'path': str(canonical / 'static_sites' / name), 'sha256': digest(path)}
    readme = out / 'README.md'
    if readme.exists():
        fragment['derived']['static-sites/README.md'] = {
            'sha256': digest(readme), 'artifact_identity': recipe['artifact_identity'],
            'schema_version': 1}
    (out / 'manifest-fragment.json').write_text(json.dumps(fragment, indent=2) + '\n')
    print(f'Static analysis recorded {len(sites)} sites.')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--manifest', type=Path, default=Path('build/stock-zisk/build-recipe.json'))
    parser.add_argument('--out', type=Path, default=Path('build/stock-zisk/static-sites'))
    args = parser.parse_args()
    collect(args.manifest, args.out)
