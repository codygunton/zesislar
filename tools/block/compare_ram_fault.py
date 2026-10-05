#!/usr/bin/env python3
"""Compare the complete RamFault switch on one fixed root and domain."""
import argparse
import asyncio
import copy
from concurrent.futures import ProcessPoolExecutor
import hashlib
import json
from pathlib import Path
import subprocess
import shutil
import time

import chain_root
import check_entry_bindings
import discovery
import entry_schema
import gen_block

SWITCH = 'ZesuSsz.Automation.Switches.RamFault'


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def primary_body(source):
    return source.split('Proof.\n', 1)[1].split('Abort.', 1)[0]


def verify_pair(off, on, historical):
    line = 'Require Import ' + SWITCH + '.\n'
    if line not in on or line in off or on.replace(line, '') != off:
        raise ValueError('The paired sources differ beyond the RamFault import')
    if primary_body(on) != primary_body(historical):
        raise ValueError('The frozen primary body changed')
    return hashlib.sha256(primary_body(on).encode()).hexdigest()


def activation_source(imports, enabled):
    rows = list(dict.fromkeys(['ZesuSsz.Automation.All', *imports]))
    if (SWITCH in rows) != enabled:
        raise ValueError('The switch imports do not match the arm')
    return '\n'.join('Require Import ' + row + '.' for row in rows) + '\n' + (
        '' if enabled else 'Fail ') + 'Check (ltac:(typeclasses eauto) : ZesuStepRamFault).\n'


def worker(job):
    arm, row, block, state, options = job
    return {'arm': arm, **asyncio.run(discovery.probe_block(row, block, state, options))}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ('root-commit', 'design', 'cfg', 'manifest', 'binding-report',
                 'primary', 'archive-index', 'build-dir', 'out'):
        parser.add_argument('--' + name, required=True)
    args = parser.parse_args()
    root = subprocess.check_output(['git', 'rev-parse', 'HEAD'], text=True).strip()
    expected = subprocess.check_output(['git', 'rev-parse', args.root_commit], text=True).strip()
    if root != expected:
        raise ValueError('The comparison root differs from the announced root')
    workspace = Path.cwd()
    design = json.loads(Path(args.design).read_text())
    cfg = json.loads(Path(args.cfg).read_text())
    manifest = json.loads(Path(args.manifest).read_text())
    previous = json.loads(Path(args.primary).read_text())
    archive = json.loads(Path(args.archive_index).read_text())
    if cfg['artifact_identity'] != manifest['artifact_identity'] or design['hashes']['selected_elf_sha256'] != manifest['elf_sha256']:
        raise ValueError('The selected code identity changed')
    check_entry_bindings.validate_report(args.binding_report, args.design, workspace)
    states, errors = entry_schema.design_states(design, workspace,
        'ZesuSsz.Stock.Closure.index_decodeItem', ['  decodeItemSelectedCode -∗'])
    ready, gaps = discovery.prepare(design, cfg, states, gen_block.address(design['entry_pc']), errors)
    if gaps or len(ready) != 24:
        raise ValueError('The paired comparison requires all 24 executable entries')
    out = Path(args.out).resolve()
    out.mkdir(parents=True, exist_ok=True)
    inputs = {str(Path(p).resolve()): digest(p) for p in (
        args.design, args.cfg, args.manifest, args.binding_report, args.primary, args.archive_index,
        __file__, discovery.__file__, chain_root.__file__, entry_schema.__file__,
        'tools/block/native_diagnostics.py', 'tools/block/setup_fallback.py',
        'tools/rocq_mcp_guarded.sh', 'tools/block/entry_check_coqc.sh', '_CoqProject')}
    from rocq_mcp import server
    from rocq_mcp import interactive
    import pytanque.client
    import pytanque.protocol
    for module in (server, interactive, pytanque.client, pytanque.protocol):
        inputs[str(Path(module.__file__).resolve())] = digest(module.__file__)
    for name in ('coqc', 'pet', 'rocq-mcp'):
        binary = shutil.which(name)
        if binary is None:
            raise ValueError('The pinned toolchain lacks ' + name)
        inputs[str(Path(binary).resolve())] = digest(binary)
    for base in ('ZesuSsz/Automation', 'ZesuSsz/Contracts', 'InstrSpecs', 'ZesuStock'):
        inputs.update({str(p.resolve()): digest(p) for p in Path(base).rglob('*.v')})
    for p in Path(args.build_dir).rglob('*.vo'):
        if p.is_file():
            inputs[str(p.resolve())] = digest(p)
    jobs, pairs = [], []
    imports = {'switch-off': set(), 'switch-on': set()}
    for row, block, original in ready:
        original['imports'] = list(dict.fromkeys(original['imports'] + previous['probe_imports']))
        for target in block['successors'] or ['decodeItemReturnAddress args']:
            sources, targets = {}, {}
            for arm in imports:
                state = copy.deepcopy(original)
                if arm == 'switch-off':
                    state['imports'] = [name for name in state['imports'] if name != SWITCH]
                source = chain_root.render_probe(state, block, chain_root.terminal_target(target))
                sources[arm], targets[arm] = source, state
                imports[arm].update(line[len('Require Import '):-1] for line in source.splitlines()
                                    if line.startswith('Require Import ') and line.endswith('.'))
            name = 'block_' + row['entry_pc'] + '_' + chain_root.boundary_label(chain_root.terminal_target(target)) + '.v'
            old = next(value for path, value in archive.items()
                       if Path(path).name == name and Path(path).parent.name == 'probes')
            if digest(old['archive_path']) != old['sha256']:
                raise ValueError('A frozen historical source changed')
            body = verify_pair(sources['switch-off'], sources['switch-on'], Path(old['archive_path']).read_text())
            pairs.append({'entry': row['entry_pc'], 'target': target, 'primary_body_sha256': body,
                          'historical_source': old,
                          'sources': {arm: hashlib.sha256(source.encode()).hexdigest() for arm, source in sources.items()}})
            old_block = next(value for value in previous['blocks'] if value['entry'] == row['entry_pc'])
            for arm in imports:
                options = {'workspace': str(workspace), 'out': str(out/arm),
                    'mcp_command': str(workspace/'tools/rocq_mcp_guarded.sh'),
                    'terminal': 'decodeItemReturnAddress args', 'seconds': 300,
                    'build_dir': str(Path(args.build_dir).resolve()), 'secondary_enabled': False,
                    'probe_targets': [target],
                    'load_before_start': old_block['outcomes'] == ['primary-unavailable']}
                jobs.append((arm, row, block, targets[arm], options))
    if len(pairs) != 38:
        raise ValueError('The comparison does not contain 38 pairs')
    activation = {}
    for arm in imports:
        path = out/(arm.replace('-', '_') + '_Activation.v')
        path.write_text(activation_source(sorted(imports[arm]), arm == 'switch-on'))
        health, result = asyncio.run(check_entry_bindings.compile_queries(workspace, path, 60))
        activation[arm] = {'source': str(path), 'sha256': digest(path), 'health': health, 'result': result}
        (out/'activation.json').write_text(json.dumps(activation, indent=2)+'\n')
        if not result.get('success'):
            raise ValueError('The switch activation check failed: ' + arm)
    started = time.monotonic()
    before = discovery.machine()
    with ProcessPoolExecutor(max_workers=6) as pool:
        results = list(pool.map(worker, jobs))
    after = discovery.machine()
    for path, expected_hash in inputs.items():
        if digest(path) != expected_hash:
            raise ValueError('A comparison input changed: ' + path)
    report = {'label': 'Full RamFault switch comparison; no sole-Assert causal claim',
        'root_commit': root, 'inputs': inputs, 'pairs': pairs, 'activation': activation,
        'historical_primary': previous['raw_report'], 'historical_comparison': 'Different root/domain; descriptive only',
        'workers': 6, 'primary_budget_seconds': 300, 'setup_budget_seconds': 60, 'proof_memory_limit_gib': 6,
        'timeout_policy': 'Reset primary deadline after setup; floor remaining seconds; exact call arguments recorded',
        'secondary_policy': 'Disabled in both primary arms; historical secondary evidence remains separate',
        'setup_policy': 'Default MCP with LOAD fallback; one LOAD-first owned start for the three historical unavailable entries',
        'elapsed_seconds': time.monotonic()-started, 'machine_before': before, 'machine_after': after,
        'results': results, 'instruction_closures': 0, 'contract_closures': 0,
        'closure_policy': 'Abstract successor handoffs do not establish contract closure'}
    path = out/'report.json'
    path.write_text(json.dumps(report, indent=2)+'\n')
    print(json.dumps({'report': str(path), 'sha256': digest(path), 'pairs': len(pairs)}))


if __name__ == '__main__':
    main()
