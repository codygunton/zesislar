#!/usr/bin/env python3
"""Compare historical imports with approved switches on one fixed root and domain."""
import argparse
import asyncio
import copy
from concurrent.futures import ProcessPoolExecutor
import hashlib
import json
import re
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


def verify_pair(off, on, historical, allowed_imports=None):
    if allowed_imports is None:
        line = 'Require Import ' + SWITCH + '.\n'
        if line not in on or line in off or on.replace(line, '') != off:
            raise ValueError('The paired sources differ beyond the RamFault import')
    else:
        imports = lambda source: {line[len('Require Import '):-1] for line in source.splitlines()
                                  if line.startswith('Require Import ') and line.endswith('.')}
        additions = imports(on) - imports(off)
        if imports(off) - imports(on) or not additions <= set(allowed_imports):
            raise ValueError('The paired sources contain an unauthorized import change')
        reduced = on
        for name in additions:
            reduced = reduced.replace('Require Import ' + name + '.\n', '')
        if reduced != off:
            raise ValueError('The paired sources differ beyond approved switch imports')
    if primary_body(on) != primary_body(historical):
        raise ValueError('The frozen primary body changed')
    return hashlib.sha256(primary_body(on).encode()).hexdigest()


def switch_class(module):
    """Resolve one declared switch class to its full source namespace."""
    if not module.startswith('ZesuSsz.Automation.Switches.'):
        raise ValueError('The activation query requires a switch module name')
    name = 'ZesuStep' + module.rsplit('.', 1)[-1]
    root = Path(__file__).resolve().parents[2]
    owners = [path for path in (root/'ZesuSsz/Automation').rglob('*.v')
              if re.search(r'^\s*Class\s+' + re.escape(name) + r'\b', path.read_text(), re.M)]
    if len(owners) != 1:
        raise ValueError('The switch class needs exactly one source declaration: ' + name)
    namespace = '.'.join(owners[0].relative_to(root).with_suffix('').parts)
    return namespace + '.' + name


def activation_source(imports, enabled, queried_switches=()):
    rows = list(dict.fromkeys(['ZesuSsz.Automation.All', *imports]))
    if (SWITCH in rows) != enabled:
        raise ValueError('The switch imports do not match the arm')
    ram_class = switch_class(SWITCH)
    source = '\n'.join('Require Import ' + row + '.' for row in rows) + '\nCheck ' + ram_class + '.\n' + (
        '' if enabled else 'Fail ') + 'Check (ltac:(typeclasses eauto) : ' + ram_class + ').\n'
    if queried_switches:
        source += 'Goal True.\nProof.\n'
        for module in queried_switches:
            if not module.startswith('ZesuSsz.Automation.Switches.') or not re.fullmatch(r'[A-Za-z_][A-Za-z_0-9]*', module.rsplit('.', 1)[-1]):
                raise ValueError('The activation query requires a switch module name')
            name = switch_class(module)
            source = source.replace('Goal True.\nProof.\n', 'Check ' + name + '.\nGoal True.\nProof.\n', 1)
            source += ('tryif (let evidence := constr:(ltac:(typeclasses eauto) : ' + name +
                       ') in idtac) then idtac "SCOPE ' + name + ' ACTIVE" else idtac "SCOPE ' + name + ' INACTIVE".\n')
        source += 'exact I.\nQed.\n'
    return source



def worker(job):
    arm, row, block, state, options = job
    return {'arm': arm, **asyncio.run(discovery.probe_block(row, block, state, options))}


APPROVED_CAPTURE_FILES = {'tools/block/compare_ram_fault.py', 'tools/block/discovery.py',
                          'tools/block/complete_goals_mcp.py', 'tools/block/complete_goals_mcp.sh', 'tools/block/feedback_mcp.py', 'tools/block/feedback_mcp.sh'}


def verify_resume_inputs(previous, current, workspace):
    changes = {}
    for path, expected in previous.items():
        actual = current.get(path)
        if actual == expected:
            continue
        try:
            relative = str(Path(path).relative_to(workspace))
        except ValueError:
            relative = path
        if relative not in APPROVED_CAPTURE_FILES:
            raise ValueError('An immutable resume input changed: ' + path)
        changes[path] = {'previous': expected, 'current': actual}
    return changes


def reuse_completed(job):
    """Reuse completed calls even when their recorder output is incomplete."""
    arm, row, block, state, options = job
    target = chain_root.terminal_target(options['probe_targets'][0])
    path = Path(options['out'])/'probes'/('block_' + row['entry_pc'] + '_' + chain_root.boundary_label(target) + '.v')
    output_path = path.with_suffix('.out')
    if not output_path.exists():
        return None
    if path.read_text() != chain_root.render_probe(state, block, target):
        raise ValueError('A completed probe source changed')
    calls = json.loads(path.with_suffix('.mcp.json').read_text())
    steps = json.loads(path.with_suffix('.steps.json').read_text())
    output = output_path.read_text()
    measurements = re.findall(r'exit=(-?\d+) ms=(\d+) rss_kb=(\d+)', output)
    if not measurements:
        raise ValueError('A recorded probe has no completion measurement')
    rc, ms, rss = map(int, measurements[-1])
    primary = [step for step in steps if step.get('label') == 'primary-unchanged-zesu_block']
    for step in primary:
        if step['arguments']['body'].strip() != 'try zesu_block.' or step['arguments']['timeout'] != 300:
            raise ValueError('A completed primary used different call arguments')
    record_path = path.with_suffix('.records.json')
    records = (json.loads(record_path.read_text()) if record_path.exists()
               else discovery.parse_capture(output, state, block, target))
    for record in records:
        if rc:
            record['outcome'] = ('automation-search-timeout' if discovery.native_diagnostics.is_primary_timeout(calls)
                                 else 'mcp-error' if primary else 'primary-unavailable')
        record.update(source_sha256=digest(path), primary_steps=steps,
                      primary_tactic_entered=bool(primary), proof_phase_entered=bool(primary),
                      contract_closed=False, closure_scope='abstract successors only',
                      performance={'rc': rc, 'wall_seconds': ms/1000, 'peak_mib': rss/1024},
                      replay_policy='Completed primary calls remain immutable; no proof replay',
                      reused_capture_inputs={str(p): digest(p) for p in
                          (path, output_path, path.with_suffix('.mcp.json'), path.with_suffix('.steps.json'))})
        if not record_path.exists():
            record['metadata_limit'] = 'Worker RSS is recorded; separate Pet diagnostics and admission timing were not saved'
    return {'arm': arm, **discovery.summarize(row, records), 'secondary_diagnostics': [], 'reused': True}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ('root-commit', 'design', 'cfg', 'manifest', 'binding-report',
                 'primary', 'archive-index', 'build-dir', 'out'):
        parser.add_argument('--' + name, required=True)
    parser.add_argument('--on-import', action='append', default=[])
    parser.add_argument('--off-policy', choices=('ram-fault-disabled', 'historical'), default='ram-fault-disabled')
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
        'tools/block/complete_goals_mcp.py', 'tools/block/complete_goals_mcp.sh', 'tools/block/feedback_mcp.py', 'tools/block/feedback_mcp.sh', 'tools/rocq_mcp_guarded.sh', 'tools/block/entry_check_coqc.sh', '_CoqProject')}
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
                if arm == 'switch-on':
                    state['imports'] = list(dict.fromkeys(state['imports'] + args.on_import))
                if arm == 'switch-off' and args.off_policy == 'ram-fault-disabled':
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
            body = verify_pair(sources['switch-off'], sources['switch-on'], Path(old['archive_path']).read_text(),
                               [SWITCH, *args.on_import] if args.on_import else None)
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
                    'feedback_dir': str(out/arm/'feedback'/Path(name).stem),
                    'complete_dir': str(out/arm/'complete'/Path(name).stem),
                    'load_before_start': old_block['outcomes'] == ['primary-unavailable']}
                jobs.append((arm, row, block, targets[arm], options))
    if len(pairs) != 38:
        raise ValueError('The comparison does not contain 38 pairs')
    activation = {}
    for arm in imports:
        path = out/(arm.replace('-', '_') + '_Activation.v')
        path.write_text(activation_source(sorted(imports[arm]), arm == 'switch-on' or args.off_policy == 'historical', args.on_import))
        health, result = asyncio.run(check_entry_bindings.compile_queries(workspace, path, 60))
        activation[arm] = {'source': str(path), 'sha256': digest(path), 'health': health, 'result': result}
        (out/'activation.json').write_text(json.dumps(activation, indent=2)+'\n')
        if not result.get('success'):
            raise ValueError('The switch activation check failed: ' + arm)
        if arm == 'switch-on' and any('SCOPE ' + switch_class(name) + ' ACTIVE' not in result.get('output', '') for name in args.on_import):
            raise ValueError('An approved ON switch is inactive')
    input_record = out/'run-inputs.json'
    resume_changes = {}
    if input_record.exists():
        prior_text = input_record.read_text()
        resume_changes = verify_resume_inputs(json.loads(prior_text), inputs, workspace)
        (out/('run-inputs-' + digest(input_record) + '.json')).write_text(prior_text)
    elif any(out.glob('*/probes/*.out')):
        # The first failed attempt predated persistent input records.
        # Its immutable source/call/output files remain bound individually.
        resume_changes['history_limit'] = 'The failed first attempt saved no complete run-input record'
    input_record.write_text(json.dumps(inputs, sort_keys=True) + '\n')
    reused, pending = [], []
    for job in jobs:
        result = reuse_completed(job)
        if result is None:
            pending.append(job)
        else:
            reused.append(result)
    started = time.monotonic()
    before = discovery.machine()
    with ProcessPoolExecutor(max_workers=6) as pool:
        results = reused + list(pool.map(worker, pending))
    after = discovery.machine()
    for path, expected_hash in inputs.items():
        if digest(path) != expected_hash:
            raise ValueError('A comparison input changed: ' + path)
    report = {'label': ('Historical baseline versus all approved switches' if args.on_import else
                         'Full RamFault switch comparison; no sole-Assert causal claim'),
        'arm_imports': {arm: sorted(names) for arm,names in imports.items()},
        'on_additions': args.on_import, 'off_policy': args.off_policy,
        'root_commit': root, 'inputs': inputs, 'pairs': pairs, 'activation': activation,
        'historical_primary': previous['raw_report'], 'historical_comparison': 'Different root/domain; descriptive only',
        'resume_input_changes': resume_changes, 'reused_boundaries': len(reused), 'new_boundaries': len(pending),
        'workers': 6, 'primary_budget_seconds': 300, 'setup_budget_seconds': 60, 'proof_memory_limit_gib': 6,
        'timeout_policy': 'Preparation receives 60 seconds. One unchanged primary sentence receives 300 seconds. Recorders receive the remaining time.',
        'historical_timeout_interpretation': {
            'original_class': 'automation-search-timeout',
            'status': 'tooling-artifact-pending-rerun',
            'leading_explanation': 'SDK division is the leading explanation for historical 21-second timeouts. The SDK divided 299 seconds across 14 sentences.'},
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
