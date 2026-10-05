#!/usr/bin/env python3
"""Measure one excluded switch against an immutable full-ON baseline."""
import argparse
import asyncio
import collections
import copy
from concurrent.futures import ProcessPoolExecutor
import hashlib
import json
from pathlib import Path
import subprocess
import time

import chain_root
import check_entry_bindings
import compare_ram_fault as comparison
import discovery
import entry_schema
import gen_block


def exclude_switch(source, module):
    line = 'Require Import ' + module + '.\n'
    if source.count(line) < 1:
        raise ValueError('The baseline must import the excluded switch')
    result = source.replace(line, '')
    if comparison.primary_body(result) != comparison.primary_body(source):
        raise ValueError('The excluded import changed the primary body')
    return result


def validate_activation(output, modules, removed):
    for module in modules:
        name = comparison.switch_class(module)
        expected = 'INACTIVE' if module == removed else 'ACTIVE'
        if 'SCOPE ' + name + ' ' + expected not in output:
            raise ValueError('The marginal activation differs: ' + module)


def write(path, value):
    path.write_text(json.dumps(value, sort_keys=True, indent=2) + '\n')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ('baseline', 'inventory', 'design', 'cfg', 'binding-report', 'historical', 'build-dir', 'out', 'integration-commit'):
        parser.add_argument('--' + name, required=True)
    parser.add_argument('--execute', action='store_true')
    args = parser.parse_args()
    workspace = Path.cwd()
    baseline = json.loads(Path(args.baseline).read_text())
    inventory = json.loads(Path(args.inventory).read_text())
    if baseline['root_commit'] != inventory['root']:
        raise ValueError('The inventory root differs from the baseline')
    root = baseline['root_commit']
    subprocess.run(['git', 'merge-base', '--is-ancestor', root, 'HEAD'], check=True)
    # Driver commits can follow the frozen root. Native sources must remain identical.
    for name, expected in baseline['inputs'].items():
        if Path(name).suffix in ('.v', '.vo') and comparison.digest(name) != expected:
            raise ValueError('A frozen native input changed: ' + name)
    frozen_inputs = {name: comparison.digest(name) for name in baseline['inputs']}
    driver_path = str((workspace/'tools/block/discovery.py').resolve())
    integrated_sha = hashlib.sha256(subprocess.check_output(
        ['git', 'show', args.integration_commit + ':tools/block/discovery.py'])).hexdigest()
    if comparison.digest(driver_path) != integrated_sha:
        raise ValueError('The integrated discovery driver differs from its approved commit')
    tool_exceptions = {}
    for name, expected in baseline['inputs'].items():
        if frozen_inputs[name] == expected:
            continue
        if name == driver_path:
            policy = 'Approved I1 integration; native branch disabled; frozen primary sources remain identical'
        elif name == str((workspace/'tools/block/complete_goals_mcp.py').resolve()):
            policy = 'Approved capture-only None repair'
        else:
            raise ValueError('An unapproved frozen input changed: ' + name)
        tool_exceptions[name] = {'measured': expected, 'current': frozen_inputs[name], 'policy': policy}
    check_entry_bindings.validate_report(args.binding_report, args.design, workspace)
    design = json.loads(Path(args.design).read_text())
    cfg = json.loads(Path(args.cfg).read_text())
    previous = json.loads(Path(args.historical).read_text())
    states, errors = entry_schema.design_states(design, workspace,
        'ZesuSsz.Stock.Closure.index_decodeItem', ['  decodeItemSelectedCode -∗'])
    ready, gaps = discovery.prepare(design, cfg, states, gen_block.address(design['entry_pc']), errors)
    if gaps or len(ready) != 24 or len(inventory['prepared_arms']) != 8:
        raise ValueError('The marginal run requires 24 entries and eight approved arms')
    out = Path(args.out).resolve()
    out.mkdir(parents=True, exist_ok=True)
    modules = baseline['on_additions']
    jobs, sources, activation, imports = [], [], {}, {}
    for arm in inventory['prepared_arms']:
        removed = arm['removed_module']
        label = 'without_' + removed.rsplit('.', 1)[-1]
        arm_imports = set()
        for row, block, original in ready:
            full = copy.deepcopy(original)
            full['imports'] = list(dict.fromkeys(full['imports'] + previous['probe_imports'] + modules))
            state = copy.deepcopy(full)
            state['imports'] = [name for name in state['imports'] if name != removed]
            for target in block['successors'] or ['decodeItemReturnAddress args']:
                successor = chain_root.terminal_target(target)
                full_source = chain_root.render_probe(full, block, successor)
                source = chain_root.render_probe(state, block, successor)
                if source != exclude_switch(full_source, removed):
                    raise ValueError('The marginal source differs beyond its import')
                full_hash = hashlib.sha256(full_source.encode()).hexdigest()
                pair = next(p for p in baseline['pairs'] if p['entry'] == row['entry_pc'] and p['target'] == target)
                if pair['sources']['switch-on'] != full_hash:
                    raise ValueError('The full-ON source differs from its committed baseline')
                name = 'block_' + row['entry_pc'] + '_' + chain_root.boundary_label(successor)
                path = out/label/'probes'/(name + '.v')
                path.parent.mkdir(parents=True, exist_ok=True)
                if path.exists() and path.read_text() != source:
                    raise ValueError('A prepared marginal source changed')
                path.write_text(source)
                arm_imports.update(line[len('Require Import '):-1] for line in source.splitlines()
                                   if line.startswith('Require Import ') and line.endswith('.'))
                sources.append({'arm': label, 'removed_module': removed, 'entry': row['entry_pc'],
                                'target': target, 'path': str(path), 'sha256': comparison.digest(path),
                                'full_on_source_sha256': full_hash, 'primary_body_sha256': pair['primary_body_sha256']})
                old = next(b for b in previous['blocks'] if b['entry'] == row['entry_pc'])
                options = {'workspace': str(workspace), 'out': str(out/label),
                           'mcp_command': str(workspace/'tools/rocq_mcp_guarded.sh'),
                           'terminal': 'decodeItemReturnAddress args', 'seconds': 300,
                           'build_dir': str(Path(args.build_dir).resolve()), 'secondary_enabled': False,
                           'probe_targets': [target], 'feedback_dir': str(out/label/'feedback'/name),
                           'complete_dir': str(out/label/'complete'/name),
                           'load_before_start': old['outcomes'] == ['primary-unavailable']}
                jobs.append((label, row, block, state, options))
        if arm_imports != set(arm['imports']):
            raise ValueError('The generated imports differ from the reviewed inventory')
        imports[label] = sorted(arm_imports)
        path = out/(label + '_Activation.v')
        path.write_text(comparison.activation_source(sorted(arm_imports), comparison.SWITCH != removed, modules))
        health, result = asyncio.run(check_entry_bindings.compile_queries(workspace, path, 60))
        activation[label] = {'source': str(path), 'sha256': comparison.digest(path), 'health': health, 'result': result}
        write(out/'activation.json', activation)
        if not result.get('success'):
            raise ValueError('The marginal activation query failed: ' + label)
        validate_activation(result.get('output', ''), modules, removed)
    inputs = {str(Path(p).resolve()): comparison.digest(p) for p in (
        args.baseline, args.inventory, args.design, args.cfg, args.binding_report, args.historical,
        __file__, discovery.__file__, comparison.__file__, 'tools/block/complete_goals_mcp.py',
        'tools/block/complete_goals_mcp.sh', 'tools/block/feedback_mcp.py', 'tools/block/feedback_mcp.sh')}
    inputs.update(frozen_inputs)
    preflight = {'approved_tool_exceptions': tool_exceptions, 'root_commit': root, 'baseline_sha256': comparison.digest(args.baseline), 'inputs': inputs,
                 'sources': sources, 'imports': imports, 'activation': activation,
                 'workers': 6, 'primary_timeout': 300, 'setup_policy': baseline['setup_policy'],
                 'baseline_replay': False, 'blocked_arms': inventory['blocked_arms']}
    write(out/'preflight.json', preflight)
    if not args.execute:
        return
    started = time.monotonic()
    before = discovery.machine()
    reused, pending = [], []
    for job in jobs:
        old = comparison.reuse_completed(job)
        (reused if old else pending).append(old if old else job)
    with ProcessPoolExecutor(max_workers=6) as pool:
        results = reused + list(pool.map(comparison.worker, pending))
    for path, expected in inputs.items():
        if comparison.digest(path) != expected:
            raise ValueError('A marginal input changed: ' + path)
    for row in sources:
        if comparison.digest(row['path']) != row['sha256']:
            raise ValueError('A marginal probe source changed')
    write(out/'report.json', {**preflight, 'results': results, 'elapsed_seconds': time.monotonic()-started,
                             'machine_before': before, 'machine_after': discovery.machine(),
                             'reused_boundaries': len(reused), 'new_boundaries': len(pending),
                             'contract_closures': 0, 'closure_policy': 'Abstract stops do not establish contract closure.'})


if __name__ == '__main__':
    main()
