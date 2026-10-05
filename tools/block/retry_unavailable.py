#!/usr/bin/env python3
"""Retry only unavailable baseline entries through LOAD and one fresh Pet start."""
import argparse
import copy
from concurrent.futures import ProcessPoolExecutor
import json
from pathlib import Path
import time
import hashlib
import subprocess

import chain_root
import check_entry_bindings
import compare_ram_fault as comparison
import discovery
import entry_schema
import gen_block


def selected_entries(baseline, arm):
    return {row['entry'] for row in baseline['blocks']
            if row['arm'] == arm and row['outcomes'] == ['primary-unavailable']}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ('baseline', 'historical', 'design', 'cfg', 'binding-report', 'build-dir', 'out', 'integration-commit'):
        parser.add_argument('--' + name, required=True)
    parser.add_argument('--execute', action='store_true')
    args = parser.parse_args()
    workspace = Path.cwd()
    baseline = json.loads(Path(args.baseline).read_text())
    previous = json.loads(Path(args.historical).read_text())
    selected = selected_entries(baseline, 'switch-on')
    if len(selected) != 12:
        raise ValueError('The frozen baseline requires exactly 12 unavailable ON entries')
    for name, expected in baseline['inputs'].items():
        if Path(name).suffix in ('.v', '.vo') and comparison.digest(name) != expected:
            raise ValueError('A frozen native input changed: ' + name)
    check_entry_bindings.validate_report(args.binding_report, args.design, workspace)
    design = json.loads(Path(args.design).read_text())
    cfg = json.loads(Path(args.cfg).read_text())
    states, errors = entry_schema.design_states(design, workspace,
        'ZesuSsz.Stock.Closure.index_decodeItem', ['  decodeItemSelectedCode -∗'])
    ready, gaps = discovery.prepare(design, cfg, states, gen_block.address(design['entry_pc']), errors)
    if gaps or len(ready) != 24:
        raise ValueError('The retry requires all 24 validated declarations')
    out = Path(args.out).resolve()
    out.mkdir(parents=True, exist_ok=True)
    sources, jobs = [], []
    for row, block, original in ready:
        if row['entry_pc'] not in selected:
            continue
        state = copy.deepcopy(original)
        state['imports'] = list(dict.fromkeys(state['imports'] + previous['probe_imports'] + baseline['on_additions']))
        for target in block['successors'] or ['decodeItemReturnAddress args']:
            source = chain_root.render_probe(state, block, chain_root.terminal_target(target))
            pair = next(p for p in baseline['pairs'] if p['entry'] == row['entry_pc'] and p['target'] == target)
            import hashlib
            expected = pair['sources']['switch-on']
            if hashlib.sha256(source.encode()).hexdigest() != expected:
                raise ValueError('The retry source differs from its frozen full-ON source')
            name = 'block_' + row['entry_pc'] + '_' + chain_root.boundary_label(chain_root.terminal_target(target))
            path = out/'probes'/(name + '.v')
            path.parent.mkdir(exist_ok=True)
            path.write_text(source)
            sources.append({'entry': row['entry_pc'], 'target': target, 'path': str(path), 'sha256': expected})
            options = {'workspace': str(workspace), 'out': str(out), 'mcp_command': str(workspace/'tools/rocq_mcp_guarded.sh'),
                       'terminal': 'decodeItemReturnAddress args', 'seconds': 300,
                       'build_dir': str(Path(args.build_dir).resolve()), 'secondary_enabled': False,
                       'probe_targets': [target], 'feedback_dir': str(out/'feedback'/name),
                       'complete_dir': str(out/'complete'/name), 'load_before_start': True}
            jobs.append(('full-on-retry', row, block, state, options))
    inputs = {name: comparison.digest(name) for name in baseline['inputs']}
    capture_exceptions = {}
    driver_path = str((workspace/'tools/block/discovery.py').resolve())
    committed_driver = subprocess.check_output(['git', 'show', args.integration_commit + ':tools/block/discovery.py'])
    integrated_sha = hashlib.sha256(committed_driver).hexdigest()
    if comparison.digest(driver_path) != integrated_sha:
        raise ValueError('The integrated discovery driver differs from its approved commit')
    for name, expected in baseline['inputs'].items():
        if inputs[name] != expected:
            if name == driver_path:
                capture_exceptions[name] = {'measured': expected, 'current': inputs[name],
                    'policy': 'Approved I1 integration; designed_successors is disabled; frozen source hashes match',
                    'integration_commit': args.integration_commit}
                continue
            if name != str((workspace/'tools/block/complete_goals_mcp.py').resolve()):
                raise ValueError('An unapproved frozen input changed: ' + name)
            capture_exceptions[name] = {'measured': expected, 'current': inputs[name],
                                        'policy': 'Approved capture-only None repair'}
    inputs.update({str(Path(p).resolve()): comparison.digest(p) for p in (
        args.baseline, args.historical, args.design, args.cfg, args.binding_report, __file__,
        discovery.__file__, 'tools/block/complete_goals_mcp.py', 'tools/block/feedback_mcp.py')})
    preflight = {'root_commit': baseline['root_commit'], 'baseline_sha256': comparison.digest(args.baseline),
                 'selected_entries': sorted(selected), 'sources': sources, 'inputs': inputs,
                 'approved_tool_exceptions': capture_exceptions,
                 'primary_timeout_seconds': 300, 'workers': 6, 'baseline_replayed': False,
                 'setup_policy': 'Shell LOAD, then one fresh owned Pet start, then unchanged isolated primary.'}
    (out/'preflight.json').write_text(json.dumps(preflight, indent=2)+'\n')
    if not args.execute:
        return
    started = time.monotonic()
    before = discovery.machine()
    with ProcessPoolExecutor(max_workers=6) as pool:
        results = list(pool.map(comparison.worker, jobs))
    for name, expected in inputs.items():
        if comparison.digest(name) != expected:
            raise ValueError('A retry input changed: ' + name)
    combined = [row for row in baseline['blocks'] if row['arm'] == 'switch-on' and row['entry'] not in selected]
    classes = {}
    for result in results:
        classes.setdefault(result['entry'], set()).update(result['outcomes'])
    combined += [{'arm': 'full-on-retry', 'entry': entry, 'outcomes': sorted(values)} for entry, values in classes.items()]
    report = {**preflight, 'results': results, 'combined_on_blocks': combined, 'elapsed_seconds': time.monotonic()-started,
              'machine_before': before, 'machine_after': discovery.machine(), 'contract_closures': 0}
    (out/'report.json').write_text(json.dumps(report, indent=2)+'\n')


if __name__ == '__main__':
    main()
