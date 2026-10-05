#!/usr/bin/env python3
"""Probe designed block entries independently through Rocq MCP.

A missing executable declaration remains a specification gap. Captures do
not establish a contract proof. The driver does not propagate exit states.
"""
from __future__ import annotations

import argparse
import asyncio
from collections import Counter
from concurrent.futures import ProcessPoolExecutor
import hashlib
import json
import os
import re
import traceback
from pathlib import Path
import sys
import threading
import time

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import chain_root
import gen_block
import entry_schema
import check_entry_bindings
import native_diagnostics
import setup_fallback


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def contract_gap(block, reason):
    return {"entry": block["entry_pc"], "entry_class": block["entry_class"],
            "outcomes": ["contract-gap"], "executed": False,
            "first_residual": {"class": "spec", "reason": reason}, "captures": []}


def prepare(design, cfg, states, root, entry_errors=None):
    blocks = chain_root.graph(cfg, root)
    declared = {gen_block.address(row["entry_pc"]): row for row in design["blocks"]}
    if len(declared) != len(design["blocks"]) or set(declared) != set(blocks):
        raise ValueError("The design and CFG do not identify the same blocks")
    ready, gaps = [], []
    for pc, row in declared.items():
        block = blocks[pc]
        if gen_block.address(row["end_pc_exclusive"]) != gen_block.address(block["end"]):
            raise ValueError("The design names a different block extent")
        if set(map(gen_block.address, row["successor_pcs"])) != set(map(gen_block.address, block["successors"])):
            raise ValueError("The design names different block successors")
        state = states.get(pc)
        if state is None:
            gaps.append(contract_gap(row, (entry_errors or {}).get(pc, "The design has no executable entry declaration")))
        elif gen_block.address(state.get("entry", -1)) != pc:
            gaps.append(contract_gap(row, "The declaration names a different entry PC"))
        elif not state.get("entry_source") or not state.get("spatial"):
            gaps.append(contract_gap(row, "The declaration lacks its source or resource predicate"))
        else:
            ready.append((row, block, state))
    return ready, gaps


def outcome(record, pc):
    value = record["outcome"]
    if value != "stalled":
        return value
    residuals = record.get('pending_goals', []) + record.get('shelved_goals', [])
    if residuals and re.match(r'^\(?\s*find_in_context\s+\(\s*FindInstrKind\b', residuals[0].get('conclusion', '')):
        return 'instruction-lookup-stall'
    locations = record.get("residual_pcs", [])
    if not locations or record.get("residual_location") == "unknown":
        return "unknown-stall"
    return "entry-stall" if all(value == pc for value in locations) else "execution-stall"


def summarize(row, captures):
    classes = sorted({outcome(record, gen_block.address(row["entry_pc"])) for record in captures})
    residual = next((goal for record in captures for goal in
                     record.get("pending_goals", []) + record.get("shelved_goals", [])), None)
    if residual is None:
        residual = next((record.get("error") for record in captures if record.get("error")), None)
    return {"entry": row["entry_pc"], "entry_class": row["entry_class"],
            "outcomes": classes, "executed": any(record.get("proof_phase_entered", True) for record in captures),
            "first_residual": residual if classes != ["setup-error"] else None,
            "setup_error": residual if classes == ["setup-error"] else None,
            "captures": captures}


def process_tree(pid):
    pending, seen = ([pid] if isinstance(pid, int) else list(pid)), set()
    rss, cpu = 0, 0
    while pending:
        value = pending.pop()
        if value in seen:
            continue
        seen.add(value)
        try:
            proc = Path('/proc') / str(value)
            pending.extend(map(int, (proc / 'task' / str(value) / 'children').read_text().split()))
            fields = (proc / 'stat').read_text().rsplit(')', 1)[1].split()
            cpu += (int(fields[11]) + int(fields[12])) / os.sysconf('SC_CLK_TCK')
            rss += int(fields[21]) * os.sysconf('SC_PAGE_SIZE') // 1024
        except (OSError, ValueError):
            pass
    return rss, cpu


def data(result):
    value = result.structuredContent
    if not isinstance(value, dict):
        raise RuntimeError('Rocq MCP returned no structured result')
    return value


def feedback(value):
    return '\n'.join(row[1] for row in value.get('feedback', []))


async def probe_block(row, block, state, options):
    from mcp import ClientSession, StdioServerParameters
    from mcp.client.stdio import stdio_client
    captures = []
    diagnostic_jobs = []
    command = options['mcp_command']
    env = {**os.environ, 'ROCQ_WORKSPACE': options['workspace'],
           'ROCQ_PET_TIMEOUT': str(options['seconds'])}
    parameters = StdioServerParameters(command=command, env=env)
    async with stdio_client(parameters) as (reader, writer):
        async with ClientSession(reader, writer) as session:
            await session.initialize()
            health = data(await session.call_tool('rocq_health', {}))
            if not health.get('ok') or not health.get('toolchain', {}).get('pet', {}).get('path'):
                raise RuntimeError('Rocq MCP has no interactive toolchain')
            for target in options.get('probe_targets', block['successors'] or [options['terminal']]):
                successor = chain_root.terminal_target(target)
                source = chain_root.render_probe(state, block, successor)
                path = Path(options['out']) / 'probes' / (
                    'block_' + row['entry_pc'] + '_' + chain_root.boundary_label(successor) + '.v')
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text(source)
                started = time.monotonic()
                deadline = started + options['seconds'] + 60
                def remaining():
                    value = int(deadline - time.monotonic())
                    if value < 1:
                        raise TimeoutError('The module time limit expired')
                    return value
                initial_rss, initial_cpu = process_tree(os.getpid())
                samples = [(initial_rss, initial_cpu)]
                pet_pids = []
                pet_diagnostics = []
                stop = threading.Event()
                def monitor():
                    while not stop.wait(0.1):
                        samples.append(process_tree([os.getpid(), *pet_pids]))
                thread = threading.Thread(target=monitor, daemon=True)
                thread.start()
                calls = []
                steps = []
                load_result = None
                proof_phase_entered = False
                error_text = None
                try:
                    if options.get('load_before_start'):
                        load_out = path.parent/'loads'/path.stem
                        load_out.mkdir(parents=True, exist_ok=True)
                        wrapper = load_out/'compiler-wrapper'
                        wrapper.write_text('#!/bin/sh\nexec ' + sys.executable + ' ' +
                                           str(Path(setup_fallback.__file__).resolve()) + ' --compiler "$@"\n')
                        wrapper.chmod(0o755)
                        load_result = await asyncio.to_thread(setup_fallback.run_one, path, load_out,
                            Path(options['build_dir']), wrapper, HERE.parent/'coqc_scratch.sh')
                        if load_result['outcome'] != 'entry-elaborated':
                            raise RuntimeError('The shell LOAD failed before the authorized fresh start')
                    opened = await native_diagnostics.measured_call(session, 'rocq_start', {
                        'workspace': options['workspace'], 'file': str(path.resolve()),
                        'theorem': 'infer_boundary', 'timeout': 60}, steps)
                    calls.append(opened)
                    if not opened.get('success') and opened.get('reason') == 'timeout' and not options.get('load_before_start'):
                        load_out = path.parent/'loads'/path.stem
                        load_out.mkdir(parents=True, exist_ok=True)
                        wrapper = load_out/'compiler-wrapper'
                        wrapper.write_text('#!/bin/sh\nexec ' + sys.executable + ' ' +
                                           str(Path(setup_fallback.__file__).resolve()) + ' --compiler \"$@\"\n')
                        wrapper.chmod(0o755)
                        load_result = await asyncio.to_thread(setup_fallback.run_one, path, load_out,
                            Path(options['build_dir']), wrapper, HERE.parent/'coqc_scratch.sh')
                    if not opened.get('success'):
                        raise RuntimeError(opened.get('error', 'Rocq MCP rejected the entry'))
                    diagnostic = data(await session.call_tool('rocq_diag', {}))
                    pet_diagnostics.append(diagnostic)
                    pid = diagnostic.get('pet', {}).get('pid')
                    if pid:
                        pet_pids.append(pid)
                    proof_phase_entered = True
                    deadline = time.monotonic() + options['seconds']
                    body = source.split('Proof.\n', 1)[1].split('Abort.', 1)[0]
                    checked = await native_diagnostics.measured_call(session, 'rocq_check', {
                        'from_state': opened['state_id'], 'body': body,
                        'timeout': remaining()}, steps, opened.get('goals'), 'primary-unchanged-zesu_block')
                    calls.append(checked)
                    pet_diagnostics.append(data(await session.call_tool('rocq_diag', {})))
                    if not checked.get('success'):
                        raise RuntimeError(checked.get('error', 'Rocq MCP rejected the probe'))
                    tail = await native_diagnostics.measured_call(session, 'rocq_check', {
                        'from_state': checked['state_id'],
                        'body': 'Abort.' + source.split('Abort.', 1)[1],
                        'timeout': remaining()}, steps, checked.get('goals'), 'primary-recorder-termination')
                    calls.append(tail)
                    if not tail.get('success'):
                        raise RuntimeError(tail.get('error', 'Rocq MCP rejected the recorder terminator'))
                    output = '\n'.join(feedback(value) for value in calls)
                    if checked.get('proof_finished'):
                        output += '\nNo more goals.\n'
                    rc = 0
                except Exception as error:
                    error_text = str(error)
                    output = '\n'.join(feedback(value) for value in calls) + '\n' + str(error)
                    rc = 1
                finally:
                    stop.set()
                    thread.join()
                elapsed = time.monotonic() - started
                peak = max((sample[0] for sample in samples), default=0)
                pet_peak = max((value.get('memory', {}).get('peak_pet_rss_mb') or 0 for value in pet_diagnostics), default=0)
                peak = max(peak, round(pet_peak * 1024))
                output += f'\nexit={rc} ms={round(elapsed * 1000)} rss_kb={peak}\n'
                path.with_suffix('.steps.json').write_text(json.dumps(steps, indent=2) + '\n')
                if native_diagnostics.is_primary_timeout(calls) and options.get('secondary_enabled', True):
                    diagnostic_jobs.append(path)
                path.with_suffix('.mcp.json').write_text(json.dumps(calls, indent=2) + '\n')
                path.with_suffix('.out').write_text(output)
                records = chain_root.parse_probe(output, state, block, successor)
                for record in records:
                    record['proof_phase_entered'] = proof_phase_entered
                    if error_text:
                        record['outcome'] = 'mcp-error' if proof_phase_entered else 'setup-error'
                        record['error'] = error_text
                        if native_diagnostics.is_primary_timeout(calls):
                            record['outcome'] = 'automation-search-timeout'
                        elif load_result and load_result['outcome'] == 'entry-elaborated':
                            record['outcome'] = 'primary-unavailable'
                    record['setup_path'] = ('coqc-scratch-LOAD/fresh-owned-Pet' if options.get('load_before_start')
                                            else 'coqc-scratch-LOAD') if load_result else 'MCP'
                    record['load_result'] = load_result
                    record['primary_steps'] = steps
                    record['failed_primary_transaction'] = next((value for value in reversed(calls) if value.get('success') is False), None)
                    record['last_successful_primary_state'] = next((value for value in reversed(calls) if value.get('success')), None)
                    record['contract_closed'] = False
                    record['closure_scope'] = 'abstract successors only'
                    record['pet_diagnostics'] = pet_diagnostics
                    record['pet_peak_mib'] = pet_peak
                    record['rss_uses_unique_processes'] = True
                    record['mcp_health'] = health
                    record['source_sha256'] = digest(path)
                    record['measurement_scope'] = 'worker descendants plus the MCP-reported Pet process; 0.1-second samples and MCP peak measurements'
                    record['elapsed_seconds'] = elapsed
                    record['cpu_seconds'] = max(0, max(sample[1] for sample in samples) - initial_cpu)
                    record['module_limit_seconds'] = options['seconds']
                    record['module_limit_gib'] = 6
                captures.extend(records)
    diagnostics = []
    for path in diagnostic_jobs:
        try:
            diagnostic = await native_diagnostics.diagnose(path, options)
        except Exception as error:
            diagnostic = {'label': 'Secondary diagnostic only', 'error': str(error)}
        diagnostic_path = path.with_suffix('.native-steps.json')
        diagnostic_path.write_text(json.dumps(diagnostic, indent=2) + '\n')
        diagnostics.append({'source': str(path), 'report': str(diagnostic_path), 'sha256': digest(diagnostic_path),
                            'result': diagnostic})
    result = summarize(row, captures)
    if result['first_residual'] is None or isinstance(result['first_residual'], str):
        failure = next((capture.get('failed_primary_transaction') for capture in captures
                        if (capture.get('failed_primary_transaction') or {}).get('goals_at_failure')), None)
        if failure:
            result['first_residual'] = {'reported_goals': failure['goals_at_failure'],
                'scope': 'MCP last-valid state from failed primary transaction',
                'failed_command': failure.get('failed_command')}
    return {**result, 'secondary_diagnostics': diagnostics}


def worker(job):
    row, block, state, options = job
    try:
        return asyncio.run(probe_block(row, block, state, options))
    except Exception as error:
        return {**summarize(row, [{'outcome': 'setup-error', 'proof_phase_entered': False, 'error': traceback.format_exc()}]),
                'executed': False}



def reuse_capture(row, block, state, previous, terminal):
    """Reuse only successful diagnostics whose complete source is unchanged."""
    old = next((value for value in previous.get('blocks', []) if value['entry'] == row['entry_pc']), None)
    if not old or not old.get('executed') or not old.get('captures'):
        return None
    targets = [chain_root.terminal_target(target) for target in block['successors'] or [terminal]]
    captures = old['captures']
    if {value['exit'] for value in captures} != {chain_root.boundary_address(target) for target in targets}:
        return None
    for target in targets:
        source_hash = hashlib.sha256(chain_root.render_probe(state, block, target).encode()).hexdigest()
        matching = [value for value in captures if value['exit'] == chain_root.boundary_address(target)]
        if not matching or any(value.get('source_sha256') != source_hash or value.get('performance', {}).get('rc') != 0 for value in matching):
            return None
    for capture in captures:
        if not capture.get('rss_uses_unique_processes'):
            capture['rss_peak_is_upper_bound'] = True
            capture['measurement_note'] = 'The initial monitor can count Pet twice; its recorded RSS is a conservative bound'
            capture['pet_peak_mib'] = max((value.get('memory', {}).get('peak_pet_rss_mb') or 0 for value in capture.get('pet_diagnostics', [])), default=None)
    result = summarize(row, captures)
    result['reused_capture'] = True
    return result


def machine():
    memory = {line.split(':')[0]: line.split(':')[1].strip()
              for line in Path('/proc/meminfo').read_text().splitlines()
              if line.startswith(('MemAvailable:', 'SwapTotal:', 'SwapFree:'))}
    return {'cpu_count': os.cpu_count(), 'load': list(os.getloadavg()),
            'memory': memory, 'cpu_ticks': Path('/proc/stat').read_text().splitlines()[0]}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--design', type=Path, required=True)
    parser.add_argument('--entries', type=Path, help='Use the frozen legacy entry records instead of the design schema')
    parser.add_argument('--trace-import', help='Use this trace module for design-schema entries')
    parser.add_argument('--code-premises', type=Path, help='Read explicit code premises for design-schema entries')
    parser.add_argument('--probe-import', action='append', default=[], help='Import an explicit module in each design-schema probe')
    parser.add_argument('--binding-report', type=Path, help='Require successful source and application validation for design-schema entries')
    parser.add_argument('--cfg', type=Path, required=True)
    parser.add_argument('--manifest', type=Path, required=True)
    parser.add_argument('--out', type=Path, required=True)
    parser.add_argument('--resume-report', type=Path)
    parser.add_argument('--terminal', required=True)
    parser.add_argument('--mcp-command', default=str(HERE.parent / 'rocq_mcp_guarded.sh'))
    parser.add_argument('--build-dir', type=Path, default=Path('_build/default').resolve().parent)
    parser.add_argument('--jobs', type=int, default=6)
    parser.add_argument('--seconds', type=int, default=300)
    args = parser.parse_args()
    if not 1 <= args.jobs <= 6 or not 1 <= args.seconds <= 300:
        parser.error('The driver permits one to six workers and at most 300 seconds per MCP call')
    if not args.entries and (not args.trace_import or not args.code_premises or not args.binding_report):
        parser.error('Design-schema entries require --trace-import, --code-premises, and --binding-report')
    if args.entries and (args.trace_import or args.code_premises or args.probe_import or args.binding_report):
        parser.error('Legacy entries already contain their probe options')
    design = json.loads(args.design.read_text())
    manifest = json.loads(args.manifest.read_text())
    cfg = json.loads(args.cfg.read_text())
    if cfg.get('artifact_identity') != manifest['artifact_identity']:
        raise ValueError('The CFG names a different artifact identity')
    if design['hashes']['selected_elf_sha256'] != manifest['elf_sha256']:
        raise ValueError('The design names a different selected ELF')
    entry_errors = {}
    if args.entries:
        states = gen_block.read_states(args.entries)
    else:
        check_entry_bindings.validate_report(args.binding_report, args.design, Path.cwd())
        states, entry_errors = entry_schema.design_states(
            design, Path.cwd(), args.trace_import, args.code_premises.read_text().splitlines())
    for module in args.probe_import:
        if not entry_schema.ROCQ_NAME.fullmatch(module):
            parser.error('The probe import is not a fully qualified Rocq name')
    for state in states.values():
        state['imports'] = list(dict.fromkeys([*state.get('imports', []), *args.probe_import]))
    ready, records = prepare(design, cfg, states,
                             gen_block.address(design['entry_pc']), entry_errors)
    def source_name(path):
        resolved = Path(path).resolve()
        return str(resolved.relative_to(Path.cwd())) if resolved.is_relative_to(Path.cwd()) else str(resolved)
    input_paths = [args.design, args.cfg, args.manifest, Path(__file__), Path(chain_root.__file__), Path(entry_schema.__file__), Path(native_diagnostics.__file__), Path(setup_fallback.__file__)]
    input_paths.append(args.entries if args.entries else args.code_premises)
    if args.binding_report:
        input_paths.append(args.binding_report)
        input_paths.extend([Path(check_entry_bindings.__file__), HERE/'entry_bindings.py', HERE/'trace_registers.py'])
    input_paths.extend(Path(module.replace('.', '/') + '.v') for module in args.probe_import
                       if Path(module.replace('.', '/') + '.v').is_file())
    input_paths.extend(path for path in (Path('_CoqProject'), Path(args.mcp_command)) if path.is_file())
    sources = {source_name(path): digest(path) for path in input_paths}
    for row in design['blocks']:
        hashes = row.get('source_hashes', {})
        for path in hashes if isinstance(hashes, dict) else []:
            # Bind actual files even when the supplied hash causes a specification gap.
            if not isinstance(path, str) or "\0" in path:
                continue
            candidate = Path(path)
            if candidate.is_file() and candidate.resolve().is_relative_to(Path.cwd()):
                sources[source_name(candidate)] = digest(candidate)
    for _, _, state in ready:
        source = Path(state['entry_source']['path'])
        if digest(source) != state['entry_source']['sha256']:
            raise ValueError('The executable entry source hash changed')
        if state['entry_source']['declaration'] not in source.read_text():
            raise ValueError('The executable entry source does not contain its declaration')
        sources[str(source)] = digest(source)
    args.out.mkdir(parents=True, exist_ok=True)
    options = {'workspace': str(Path.cwd()), 'out': str(args.out.resolve()),
               'mcp_command': args.mcp_command, 'terminal': args.terminal, 'seconds': args.seconds,
               'build_dir': str(args.build_dir.resolve())}
    reused = []
    if args.resume_report:
        previous = json.loads(args.resume_report.read_text())
        for path, expected in previous['inputs'].items():
            if Path(path).name not in ('discovery.py', 'chain_root.py') and digest(path) != expected:
                raise ValueError('A captured proof input changed')
        pending = []
        for row, block, state in ready:
            cached = reuse_capture(row, block, state, previous, args.terminal)
            if cached:
                reused.append(cached)
            else:
                pending.append((row, block, state))
        ready = pending
        sources[str(args.resume_report)] = digest(args.resume_report)
    before, started = machine(), time.monotonic()
    with ProcessPoolExecutor(max_workers=args.jobs) as pool:
        records += reused + list(pool.map(worker, [(row, block, state, options) for row, block, state in ready]))
    elapsed = time.monotonic() - started
    designed = {row['entry_pc']: row for row in design['blocks']}
    for record in records:
        row = designed[record['entry']]
        state = states.get(gen_block.address(record['entry']))
        roles = []
        if record['entry'] == design['entry_pc']:
            roles.append('root')
        if row.get('invariant_hint'):
            roles.append('loop-header')
        if len(row.get('incoming_edges', [])) > 1:
            roles.append('join')
        if row.get('return_clause'):
            roles.append('return')
        record['entry_roles'] = roles or ['block']
        record['entry_provenance'] = {
            'design_sha256': digest(args.design),
            'design_entry_sha256': hashlib.sha256(json.dumps(row, sort_keys=True).encode()).hexdigest(),
            'executable_source': state.get('entry_source') if state else None,
            'resource_predicates': state.get('spatial') if state else None}
        if not args.entries:
            record['entry_provenance']['design_contract'] = {
                key: row[key] for key in sorted(entry_schema.FIELDS) if key in row}
    measurements = [capture['performance'] for row in records for capture in row['captures'] if 'performance' in capture]
    report = {'schema': 1, 'label': 'Phase 1 WP5 designed-entry discovery; no proof completion claim',
              'capture_only': True, 'probe_imports': args.probe_import, 'artifact_identity': manifest['artifact_identity'],
              'selected_elf_sha256': manifest['elf_sha256'], 'inputs': sources, 'block_count': len(design['blocks']),
              'workers': args.jobs, 'new_block_runs': len(ready), 'reused_block_runs': len(reused),
              'elapsed_seconds': elapsed,
              'resumed_capture_run_seconds': previous['elapsed_seconds'] if args.resume_report else None,
              'peak_worker_mib_upper_bound': max((value['peak_mib'] for value in measurements), default=None),
              'peak_pet_mib': max((capture.get('pet_peak_mib') or 0 for row in records for capture in row['captures']), default=None),
              'machine_before': before, 'machine_after': machine(),
              'classes': dict(Counter(value for row in records for value in row['outcomes'])),
              'blocks': sorted(records, key=lambda row: gen_block.address(row['entry']))}
    chain_root.atomic_json(args.out / 'report.json', report)
    print(json.dumps({'report': str(args.out / 'report.json'), 'sha256': digest(args.out / 'report.json'),
                      'classes': report['classes'], 'elapsed_seconds': elapsed}))
    return 1 if any(report['classes'].get(key) for key in ('error', 'setup-error', 'mcp-error', 'primary-unavailable', 'automation-search-timeout')) else 0


if __name__ == '__main__':
    raise SystemExit(main())
