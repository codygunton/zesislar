#!/usr/bin/env python3
"""Check or re-extract the closed region windows of the access-region policies.

A trace-only policy packet (`build/stock-zisk/*-policy/regions.json.gz`)
fixes each memory region's integer window. The windows come from the
selected MachineMap, which `machine_map/generate.py` renders from the ELF.
A packet extracted for one ELF silently constrains the traces of another:
on the compressed-free dry run the eql packet still named the old .rodata
window and every regenerated eql trace carried it.

`--check` evaluates each window's MachineMap expression against
ZesuSsz/Contracts/Machine.v and fails on any difference, on a PATH-MAP that
binds another ELF, and on a Makefile or test pin that names another packet
or map. `--write` re-extracts the windows, archives the current Machine.v
as the declaration source, and rewrites the packet, its PATH-MAP and those
pins. The packet is a gzip of `json.dumps(indent=2)` at level 9 with mtime 0.
"""
import argparse
import gzip
import hashlib
import json
from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(ROOT / 'tools'))
from machine_config import read_machine  # noqa: E402

BUILD = ROOT / 'build/stock-zisk'
MACHINE = ROOT / 'ZesuSsz/Contracts/Machine.v'
PINS = [ROOT / 'Makefile', ROOT / 'tools/test_function_preparation.py']
# Windows of packets that store integers without their MachineMap expression.
NAMED = {'RAM': ('mapRamBase defaultMap', 'machineRamEnd defaultMap'),
         'INPUT_BUFFER': ('mapInputBufferAddress defaultMap',
                          'mapInputBufferAddress defaultMap + mapInputCapacity defaultMap'),
         'RODATA': ('mapRodataBase defaultMap', 'mapRodataEnd defaultMap')}


def sha(data):
    return hashlib.sha256(data).hexdigest()


def evaluate(expression, machine):
    """Evaluate a sum of `field defaultMap` terms; machineRamEnd is base plus size."""
    total = 0
    for term in expression.split('+'):
        field = re.fullmatch(r'\s*(\w+) defaultMap\s*', term)
        if not field:
            raise ValueError(f'Unsupported window expression: {expression}')
        name = field[1]
        total += machine['mapRamBase'] + machine['mapRamSize'] if name == 'machineRamEnd' else machine[name]
    return total


def policies(build=BUILD):
    return sorted(path.parent for path in build.glob('*-policy/regions.json.gz'))


def load(policy):
    archive = (policy / 'regions.json.gz').read_bytes()
    source_map = json.loads((policy / 'PATH-MAP.json').read_text())
    return archive, json.loads(gzip.decompress(archive)), source_map


def windows(packet):
    """Yield (name, stored (lo, hi), expressions, setter) for every closed window."""
    if packet.get('regions') is not None:
        for name, row in packet['regions'].items():
            def store(lo, hi, row=row):
                row.update(lower=str(lo), upper=str(hi))
            yield name, (int(row['lower']), int(row['upper'])), NAMED[name], store
    for declaration in packet.get('source_declarations', []):
        for name, row in declaration.get('closed_region_values', {}).items():
            def store(lo, hi, row=row):
                row.update(lo=lo, hi=hi)
            yield name, (row['lo'], row['hi']), (row['lower'], row['upper']), store


def problems(policy, machine, elf_sha, pins):
    archive, packet, source_map = load(policy)
    found = []
    for name, stored, (lower, upper), _ in windows(packet):
        expected = (evaluate(lower, machine), evaluate(upper, machine))
        if stored != expected:
            found.append(f'{policy.name} {name} window {stored[0]:#x}..{stored[1]:#x} '
                         f'differs from the selected map {expected[0]:#x}..{expected[1]:#x}')
    elf = source_map.get('input_files', {}).get('elf', {})
    if elf and elf.get('sha256') != elf_sha:
        found.append(f'{policy.name} PATH-MAP binds ELF {elf.get("sha256")}, not {elf_sha}')
    record = source_map['archives']['regions.json.gz']
    if record['sha256'] != sha(archive) or record['payload_sha256'] != sha(gzip.decompress(archive)):
        found.append(f'{policy.name} PATH-MAP archive binding differs from regions.json.gz')
    relative = policy.relative_to(ROOT).as_posix()
    expected_pins = {f'{relative}/regions.json.gz': record['payload_sha256'],
                     f'{relative}/PATH-MAP.json': sha((policy / 'PATH-MAP.json').read_bytes())}
    for path in pins:
        text = path.read_text()
        for target, digest in expected_pins.items():
            for value in re.findall(re.escape(target) + r'["\s\\,]+[-a-z"]*-sha256["\s,]+([0-9a-f]{64})', text):
                if value != digest:
                    found.append(f'{path.relative_to(ROOT)} pins {target} at {value}, not {digest}')
    return found


def rewrite(policy, machine, machine_path, pins):
    """Re-extract every window; return True when the packet changed."""
    archive, packet, source_map = load(policy)
    old_payload, old_map = sha(gzip.decompress(archive)), sha((policy / 'PATH-MAP.json').read_bytes())
    changed = False
    for name, stored, (lower, upper), store in windows(packet):
        expected = (evaluate(lower, machine), evaluate(upper, machine))
        if stored != expected:
            store(*expected)
            changed = True
    if not changed:
        return False
    source = machine_path.read_bytes()
    archived = f'sources/{sha(source)}.v'
    (policy / archived).write_bytes(source)
    relative_machine = machine_path.relative_to(ROOT).as_posix()
    for declaration in packet.get('source_declarations', []):
        if 'closed_region_values' in declaration:
            declaration['file'] = {'path': relative_machine, 'sha256': sha(source)}
    source_map['paths'][relative_machine] = {'path': archived, 'sha256': sha(source)}
    payload = (json.dumps(packet, indent=2) + '\n').encode()
    compressed = gzip.compress(payload, compresslevel=9, mtime=0)
    (policy / 'regions.json.gz').write_bytes(compressed)
    source_map['archives']['regions.json.gz'] = {'sha256': sha(compressed), 'payload_sha256': sha(payload)}
    (policy / 'PATH-MAP.json').write_text(json.dumps(source_map, indent=2) + '\n')
    new_payload, new_map = sha(payload), sha((policy / 'PATH-MAP.json').read_bytes())
    for path in pins:
        text = path.read_text()
        path.write_text(text.replace(old_payload, new_payload).replace(old_map, new_map))
    return True


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--build', type=Path, default=BUILD)
    parser.add_argument('--machine', type=Path, default=MACHINE)
    parser.add_argument('--write', action='store_true')
    args = parser.parse_args()
    build, machine_path = args.build.resolve(), args.machine.resolve()
    machine = read_machine(machine_path.read_text())
    elf_sha = json.loads((build / 'build-recipe.json').read_text())['elf_sha256']
    if args.write:
        for policy in policies(build):
            if rewrite(policy, machine, machine_path, PINS):
                print('re-extracted', policy.relative_to(ROOT))
    found = [item for policy in policies(build) for item in problems(policy, machine, elf_sha, PINS)]
    if found:
        sys.exit('Region policy windows differ from the selected ELF:\n  ' + '\n  '.join(found))
    print(f'Region policy windows match the selected map in {len(policies(build))} policies')


if __name__ == '__main__':
    main()
