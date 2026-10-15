#!/usr/bin/env python3
"""Extract register events from manifest-bound native Islaris traces."""
import hashlib
from pathlib import Path
import re


TOKEN = re.compile(r'\(\*|\*\)|"(?:[^"\n]|"")*"|[A-Za-z_][A-Za-z0-9_\']*|[0-9]+|\S')


def tokens(text):
    """Exclude nested comments without treating strings as constructor names."""
    result, depth = [], 0
    for match in TOKEN.finditer(text):
        value = match.group()
        if value == '(*':
            depth += 1
        elif value == '*)':
            if not depth:
                raise ValueError('The source has an unmatched comment end')
            depth -= 1
        elif not depth:
            result.append(value)
    if depth:
        raise ValueError('The source has an unfinished comment')
    return result


def events(text):
    sequence = tokens(text)
    read, written, assumptions = set(), set(), set()
    in_assume = False
    for index, value in enumerate(sequence):
        if value == 'Assume':
            in_assume = True
        if sequence[index:index + 3] == [':', 't', ':']:
            in_assume = False
        if value == 'AVal_Var' and not in_assume:
            continue
        if value not in ('ReadReg', 'WriteReg', 'AVal_Var'):
            continue
        if index + 1 == len(sequence) or not sequence[index + 1].startswith('"'):
            raise ValueError('The trace has a nonliteral register name')
        register = sequence[index + 1][1:-1].replace('""', '"')
        if not register:
            raise ValueError('The trace has an empty register name')
        (read if value == 'ReadReg' else written if value == 'WriteReg' else assumptions).add(register)
    return {'regs_read': sorted(read), 'regs_written': sorted(written)}, sorted(assumptions)


def bound_trace(path, pc, manifest):
    path = Path(path)
    name = str(path)
    record = manifest['project_derived'].get(name)
    if not record or record.get('artifact_identity') != manifest['artifact_identity']:
        raise ValueError('The manifest does not bind the instruction trace: ' + name)
    data = path.read_bytes()
    digest = hashlib.sha256(data).hexdigest()
    if digest != record.get('sha256'):
        raise ValueError('The native trace hash changed: ' + name)
    source = data.decode()
    if not re.search(r'\bDefinition\s+a' + format(pc, 'x') + r'\s*:\s*isla_trace\s*:=', source):
        raise ValueError('The native trace declares a different instruction PC')
    footprint, assumptions = events(source)
    return footprint, assumptions, digest


def extract(cfg, root_pc, trace_dir, manifest):
    functions = [row for row in cfg['functions'] if int(str(row['entry']), 0) == root_pc]
    if len(functions) != 1 or cfg.get('artifact_identity') != manifest['artifact_identity']:
        raise ValueError('The CFG does not identify the selected function and artifact')
    function = functions[0]
    instruction_pcs = [int(str(row['pc']), 0) for row in function['rows']]
    if len(set(instruction_pcs)) != len(instruction_pcs):
        raise ValueError('The CFG contains duplicate instruction PCs')
    instructions, sources = {}, {}
    for pc in instruction_pcs:
        path = Path(trace_dir) / ('a' + format(pc, 'x') + '.v')
        footprint, assumptions, digest = bound_trace(path, pc, manifest)
        instructions[pc] = {**footprint, 'assumption_references': assumptions}
        sources[str(path)] = digest
    assigned, blocks = set(), []
    for row in function['blocks']:
        start, end = int(str(row['start']), 0), int(str(row['end']), 0)
        pcs = [pc for pc in instruction_pcs if start <= pc < end]
        if not pcs or assigned.intersection(pcs):
            raise ValueError('The CFG has an empty or overlapping block')
        assigned.update(pcs)
        footprint = {key: sorted({reg for pc in pcs for reg in instructions[pc][key]})
                     for key in ('regs_read', 'regs_written')}
        assumed = {reg for pc in pcs for reg in instructions[pc]['assumption_references']}
        footprint['regs_assumed'] = sorted(assumed - set(footprint['regs_read']) - set(footprint['regs_written']))
        blocks.append({'entry_pc': hex(start), **footprint})
    if assigned != set(instruction_pcs):
        raise ValueError('The CFG leaves instructions outside its blocks')
    return blocks, {hex(pc): row for pc, row in instructions.items()}, sources


def main():
    import argparse
    import json
    import time
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--design', type=Path, required=True)
    parser.add_argument('--cfg', type=Path, required=True)
    parser.add_argument('--manifest', type=Path, required=True)
    parser.add_argument('--trace-dir', type=Path, required=True)
    parser.add_argument('--out', type=Path, required=True)
    args = parser.parse_args()
    started = time.monotonic()
    design = json.loads(args.design.read_text())
    cfg = json.loads(args.cfg.read_text())
    manifest = json.loads(args.manifest.read_text())
    if design['hashes']['selected_elf_sha256'] != manifest['elf_sha256']:
        raise ValueError('The design names a different ELF')
    root_pc = int(str(design['entry_pc']), 0)
    blocks, instructions, sources = extract(cfg, root_pc, args.trace_dir, manifest)
    if {row['entry_pc'] for row in blocks} != {row['entry_pc'] for row in design['blocks']}:
        raise ValueError('The design and CFG identify different blocks')
    inputs = {str(path): hashlib.sha256(path.read_bytes()).hexdigest()
              for path in (args.design, args.cfg, args.manifest, Path(__file__))}
    inputs.update(sources)
    args.out.mkdir(parents=True, exist_ok=True)
    design_fragment = {'blocks': blocks}
    cfg_fragment = {'functions': [{'entry': root_pc, 'blocks': [
        {'start': int(row['entry_pc'], 0), **{key: row[key] for key in ('regs_read', 'regs_written', 'regs_assumed')}}
        for row in blocks]}]}
    report = {'schema': 1, 'label': 'Native trace register footprints; no execution or proof completion claim',
              'artifact_identity': manifest['artifact_identity'], 'elf_sha256': manifest['elf_sha256'],
              'inputs': inputs, 'block_count': len(blocks), 'instruction_count': len(instructions),
              'event_policy': 'Explicit native ReadReg and WriteReg events include PC',
              'assumption_policy': 'regs_assumed contains Assume references absent from explicit events in that block',
              'blocks': blocks, 'instructions': instructions, 'elapsed_seconds': time.monotonic()-started,
              'workers': 1}
    outputs = {'design-fragment.json': design_fragment, 'cfg-fragment.json': cfg_fragment,
               'report.json': report}
    for name, value in outputs.items():
        (args.out/name).write_text(json.dumps(value, indent=2)+'\n')
    fragment = {'schema': 1, 'artifact_identity': manifest['artifact_identity'],
                'manifest_binding_pending': True, 'inputs': inputs,
                'derived': {str(args.out/name): hashlib.sha256((args.out/name).read_bytes()).hexdigest() for name in outputs}}
    (args.out/'manifest-fragment.json').write_text(json.dumps(fragment, indent=2)+'\n')
    print(json.dumps({'report': str(args.out/'report.json'),
                      'sha256': hashlib.sha256((args.out/'report.json').read_bytes()).hexdigest(),
                      'blocks': len(blocks), 'instructions': len(instructions)}))
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
