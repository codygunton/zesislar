#!/usr/bin/env python3
"""Attempt one fresh owned Pet start after LOAD for recorded setup failures."""
import argparse
import asyncio
from concurrent.futures import ProcessPoolExecutor
import hashlib
import json
from pathlib import Path
import time

import chain_root
import discovery
import entry_schema
import gen_block
import check_entry_bindings


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def worker(job):
    row, block, state, options = job
    return asyncio.run(discovery.probe_block(row, block, state, options))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ('primary', 'archive-index', 'design', 'cfg', 'manifest', 'binding-report', 'build-dir', 'out'):
        parser.add_argument('--' + name, type=Path, required=True)
    parser.add_argument('--jobs', type=int, default=3)
    args = parser.parse_args()
    if not 1 <= args.jobs <= 6:
        parser.error('The fresh-start pass permits at most six workers')
    primary = json.loads(args.primary.read_text())
    archive = json.loads(args.archive_index.read_text())
    design = json.loads(args.design.read_text())
    cfg = json.loads(args.cfg.read_text())
    manifest = json.loads(args.manifest.read_text())
    if design['hashes']['selected_elf_sha256'] != manifest['elf_sha256'] or cfg['artifact_identity'] != manifest['artifact_identity']:
        raise ValueError('The selected code inputs disagree')
    check_entry_bindings.validate_report(args.binding_report, args.design, Path.cwd())
    states, errors = entry_schema.design_states(design, Path.cwd(),
        'ZesuSsz.Stock.Closure.index_decodeItem', ['  decodeItemSelectedCode -∗'])
    ready, gaps = discovery.prepare(design, cfg, states, gen_block.address(design['entry_pc']), errors)
    if gaps:
        raise ValueError('The fresh-start design has a contract gap')
    unavailable = {row['entry'] for row in primary['blocks'] if row['outcomes'] == ['primary-unavailable']}
    if len(unavailable) != 3:
        raise ValueError('The accepted primary report does not identify three unavailable blocks')
    args.out.mkdir(parents=True, exist_ok=True)
    inputs = {str(path): digest(path) for path in
              (args.primary, args.archive_index, args.design, args.cfg, args.manifest,
               args.binding_report, Path(__file__), Path(discovery.__file__))}
    jobs = []
    for row, block, state in ready:
        if row['entry_pc'] not in unavailable:
            continue
        state['imports'] = list(dict.fromkeys(state['imports'] + primary['probe_imports']))
        for target in block['successors']:
            name = 'block_' + row['entry_pc'] + '_' + chain_root.boundary_label(chain_root.terminal_target(target)) + '.v'
            original = next(record for path, record in archive.items() if Path(path).name == name)
            rendered = chain_root.render_probe(state, block, chain_root.terminal_target(target)).encode()
            if hashlib.sha256(rendered).hexdigest() != original['sha256']:
                raise ValueError('The fresh primary source differs from the frozen source')
            options = {'workspace': str(Path.cwd()), 'out': str(args.out.resolve()),
                       'mcp_command': str(Path('tools/rocq_mcp_guarded.sh').resolve()),
                       'terminal': 'decodeItemReturnAddress args', 'seconds': 300,
                       'build_dir': str(args.build_dir.resolve()), 'load_before_start': True,
                       'secondary_enabled': False, 'probe_targets': [target]}
            jobs.append((row, block, state, options))
    started = time.monotonic()
    with ProcessPoolExecutor(max_workers=args.jobs) as pool:
        results = list(pool.map(worker, jobs))
    for path, expected in inputs.items():
        if digest(path) != expected:
            raise ValueError('A fresh-start input changed during execution')
    report = {'label': 'One fresh owned Pet after LOAD; unchanged primary body; prior primary results preserved',
              'inputs': inputs, 'selected_blocks': sorted(unavailable), 'workers': args.jobs,
              'elapsed_seconds': time.monotonic() - started, 'results': results,
              'raw_primary_report': primary['raw_report'], 'configured_primary_budget_seconds': 300,
              'timeout_policy': 'Integer flooring of remaining primary budget; exact arguments recorded per call',
              'instruction_closures': 0, 'contract_closures': 0}
    output = args.out/'report.json'
    output.write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps({'report': str(output), 'sha256': digest(output), 'probes': len(results)}))


if __name__ == '__main__':
    main()
