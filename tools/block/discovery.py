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
import subprocess
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
from launch_imports import validate_launch_imports


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


def feedback(value, directory=None):
    rows = []
    for _, displayed in value.get('feedback', []):
        raw = displayed
        if directory:
            key = hashlib.sha256(displayed.encode()).hexdigest()
            path = Path(directory)/(key + '.json')
            if path.exists():
                exported = json.loads(path.read_text())
                if exported['display_sha256'] != key or hashlib.sha256(exported['raw'].encode()).hexdigest() != exported['raw_sha256']:
                    raise ValueError('The feedback export hash does not match')
                raw = exported['raw']
        rows.append(raw)
    return '\n'.join(rows)


def parse_capture(output, state, block, successor):
    """Keep malformed recorder output separate from primary proof outcomes."""
    try:
        return chain_root.parse_probe(output, state, block, successor)
    except ValueError as error:
        return [{'entry': hex(gen_block.address(block['start'])),
                 'exit': chain_root.boundary_address(successor),
                 'outcome': 'capture-error', 'error': str(error),
                 'raw_goals': output, 'pending_goals': [], 'shelved_goals': [],
                 'inherited_debts': chain_root.inherited_debts(state),
                 'capture_complete': False, 'contract_closed': False}]


def native_boundary_closed(evidence, rendered, block):
    """Count only compiled, debt-free proofs of every designed boundary."""
    import successor_entailment
    if (evidence.get('outcome') != 'verified' or not evidence.get('block_closed') or
            rendered.get('scope') != 'unproved native designed boundary'):
        return False
    if set(rendered.get('successors', [])) != {hex(gen_block.address(pc)) for pc in block['successors']}:
        return False
    if not block['successors'] and rendered.get('terminal_scope') != 'existing owned Level1 continuation; no added image continuation':
        return False
    if not isinstance(evidence.get('inherited_debts'), dict) or any(evidence['inherited_debts'].values()):
        return False
    try:
        groups = successor_entailment.debt_groups(evidence['debt_groups']['groups'])
        if not groups['empty'] or digest(evidence['source']) != evidence['source_sha256']:
            return False
    except (KeyError, OSError, TypeError, ValueError):
        return False
    calls = evidence.get('calls', [])
    compiled = [c for c in calls if c['tool'] == 'rocq_compile_file']
    verified = [c for c in calls if c['tool'] == 'rocq_verify']
    primaries = [c for c in calls if c['tool'] == 'rocq_check' and
                 c['arguments'].get('body', '').strip() == 'try zesu_block.']
    return (len(compiled) == len(verified) == len(primaries) == 1 and
            compiled[0]['result'].get('success') and verified[0]['result'].get('success') and
            verified[0]['result'].get('assumptions') == [] and
            primaries[0]['arguments'].get('timeout') == 300 and
            primaries[0]['result'].get('success'))


def designed_terminal(block, options):
    if block['successors']:
        return None
    if options.get('terminal_descriptor') is not None:
        return options['terminal_descriptor']
    owner = 'ZesuSsz/Contracts/DecodeItemBranchEntries.v'
    return {'kind': 'owned_continuation', 'address': options['terminal'],
            'definition': 'ZesuSsz.Contracts.DecodeItemBranchEntries.decodeItemBranchContinuation',
            'source_hashes': {owner: digest(Path(options['workspace'])/owner)}}



def load_terminal_descriptor(path, address, root):
    """Validate an explicit owned continuation through the existing entry schema."""
    import successor_entailment
    value = json.loads(Path(path).read_text())
    if not isinstance(value, dict) or value.get('kind') != 'owned_continuation':
        raise ValueError('The terminal descriptor must name an owned continuation')
    if value.get('address') != address:
        raise ValueError('The terminal descriptor names a different terminal address')
    chain_root.terminal_target(address)
    successor_entailment.designed_target({'entry_pc': '0x0',
        'entry_definition': value['definition'], 'resource_predicate': value['definition'],
        'binders': [], 'arguments': [], 'source_hashes': value['source_hashes']}, root)
    return value


def reuse_native_capture(row, block, state, previous, options):
    """Reuse a native attempt only when its exact obligation remains unchanged."""
    import copy
    import successor_entailment
    candidates = previous.get('blocks', [previous])
    old = next((item for item in candidates if item['entry'] == row['entry_pc']), None)
    if old is None or len(old.get('captures', [])) != 1:
        return None
    bound = old['captures'][0].get('native_evidence')
    if not bound or digest(bound['path']) != bound['sha256']:
        raise ValueError('The reused native evidence changed')
    evidence = json.loads(Path(bound['path']).read_text())
    design = json.loads(Path(options['design']).read_text())
    rendered = successor_entailment.native_boundary_source(state, block, design,
        Path(options['workspace']), terminal=designed_terminal(block, options))
    expected = hashlib.sha256(rendered['source'].encode()).hexdigest()
    if expected != evidence['source_sha256'] or digest(evidence['source']) != expected:
        raise ValueError('The reused native obligation changed')
    for exported in evidence.get('exports', []):
        if not exported.get('success') or digest(exported['path']) != exported['sha256']:
            raise ValueError('A reused native goal export changed or is unavailable')
    primary = [call for call in evidence['calls'] if call['tool'] == 'rocq_check' and
               call['arguments'].get('body', '').strip() == 'try zesu_block.']
    if len(primary) != 1 or primary[0]['arguments'].get('timeout') != 300:
        raise ValueError('The reused native attempt has different primary arguments')
    result = copy.deepcopy(old)
    result['reused_native_attempt'] = True
    result['reuse_scope'] = 'Identical native source and immutable primary/goal records; no proof replay'
    return result


async def fallback_designed_block(row, state, rendered, options, base, mcp_attempt, started):
    """Use coqc only after a failed Pet entry, with the same native statement."""
    import coqc_primary
    evidence = await asyncio.to_thread(coqc_primary.run_primary, rendered,
        base/'coqc-fallback', options['build_dir'],
        inherited_debts=chain_root.inherited_debts(state), seconds=options['seconds'])
    evidence['failed_mcp_setup'] = mcp_attempt
    evidence['performance'] = {'wall_seconds': time.monotonic()-started,
        'peak_mib': (evidence.get('compiler') or {}).get('peak_rss_kib', 0)/1024,
        'scope': 'Owned coqc compiler; failed-start Pet memory remains unknown'}
    chain_root.atomic_json(base/'fallback-evidence.json', evidence)
    capture = {'outcome': evidence['outcome'],
        'proof_phase_entered': evidence['primary_tactic_entered'],
        'pending_goals': evidence.get('active_goals') or [], 'shelved_goals': [],
        'inherited_debts': evidence['inherited_debts'],
        'performance': evidence['performance'],
        'native_evidence': {'path': str(base/'fallback-evidence.json'),
            'sha256': digest(base/'fallback-evidence.json')},
        'block_closed': evidence['block_closed'], 'contract_closed': False,
        'source_sha256': evidence['source_sha256']}
    return {**summarize(row, [capture]), 'block_closed': evidence['block_closed'],
        'successor_policy': 'Actual designed entries; root parameters remain fixed',
        'secondary_diagnostics': []}


async def probe_designed_block(row, block, state, options):
    """Run one native boundary proof through an owned guarded MCP session."""
    import successor_entailment
    design = json.loads(Path(options['design']).read_text())
    terminal = designed_terminal(block, options)
    rendered = successor_entailment.native_boundary_source(
        state, block, design, Path(options['workspace']), enabled=True,
        terminal=terminal)
    validate_launch_imports(rendered['source'], design.get('function'), options['workspace'])
    from mcp import ClientSession, StdioServerParameters
    from mcp.client.stdio import stdio_client
    base = Path(options['out'])/'native'/('block_' + row['entry_pc'])
    base.mkdir(parents=True, exist_ok=True)
    path = base/'Boundary.v'
    env = {**os.environ, 'ROCQ_WORKSPACE': options['workspace'],
           'ROCQ_PET_TIMEOUT': str(options['seconds']),
           'ZESU_ROCQ_MCP_BINARY': str(HERE/'complete_goals_mcp.sh'),
           'ZESU_MCP_PYTHON': sys.executable,
           'ZESU_COMPLETE_GOAL_DIR': str(base/'complete'),
           'ZESU_FEEDBACK_DIR': str(base/'feedback')}
    parameters = StdioServerParameters(command=options['mcp_command'], env=env)
    pet_pids, diagnostics, samples = [], [], []
    stop = threading.Event()
    def monitor():
        while not stop.wait(0.1):
            samples.append(process_tree([os.getpid(), *pet_pids]))
    thread = threading.Thread(target=monitor, daemon=True)
    started = time.monotonic()
    thread.start()
    try:
        async with stdio_client(parameters) as streams:
            async with ClientSession(*streams) as session:
                await session.initialize()
                class ObservedSession:
                    async def call_tool(self, tool, arguments):
                        result = await session.call_tool(tool, arguments)
                        if tool == 'rocq_start' and data(result).get('success'):
                            try:
                                diagnostic = data(await session.call_tool('rocq_diag', {}))
                                diagnostics.append(diagnostic)
                                pid = diagnostic.get('pet', {}).get('pid')
                                if pid:
                                    pet_pids.append(pid)
                            except Exception as error:
                                diagnostics.append({'error': str(error), 'scope': 'read-only diagnostics'})
                        return result
                evidence = await successor_entailment.check_boundary(
                    ObservedSession(), rendered, path, options['workspace'],
                    inherited_debts=chain_root.inherited_debts(state), seconds=options['seconds'])
    finally:
        stop.set()
        thread.join()
    if evidence.get('residual_class') == 'entry_unavailable':
        return await fallback_designed_block(row, state, rendered, options, base, evidence, started)
    elapsed = time.monotonic()-started
    closed = native_boundary_closed(evidence, rendered, block)
    outcome_class = ('native-boundary-closed' if closed else 'conditional-boundary'
                     if evidence['outcome'] == 'conditional' else 'native-residual'
                     if evidence['outcome'] == 'residual' else 'primary-unavailable'
                     if evidence.get('residual_class') == 'entry_unavailable' else 'native-evidence-unavailable')
    native_goals = evidence.get('debt_groups', {}).get('groups', {})
    residuals = [*native_goals.get('goals', []), *native_goals.get('shelf', []),
                 *native_goals.get('given_up', [])]
    for frame in native_goals.get('stack', []):
        residuals.extend([*frame[0], *frame[1]])
    performance = {'wall_seconds': elapsed, 'peak_mib': max((v[0] for v in samples), default=0)/1024,
                   'scope': 'Worker descendants and learned Pet PIDs; failed-start Pet memory can be unknown'}
    evidence.update(block_closed=bool(closed), contract_closed=False, performance=performance,
                    pet_diagnostics=diagnostics, owned_pet_pids=pet_pids,
                    source_sha256=digest(path), session_directory=str(base/'complete'))
    chain_root.atomic_json(base/'evidence.json', evidence)
    capture = {'outcome': outcome_class, 'proof_phase_entered': any(
        c['tool'] == 'rocq_check' and c['arguments'].get('body', '').strip() == 'try zesu_block.'
        for c in evidence.get('calls', [])), 'pending_goals': residuals, 'shelved_goals': [],
        'inherited_debts': chain_root.inherited_debts(state), 'performance': performance,
        'native_evidence': {'path': str(base/'evidence.json'), 'sha256': digest(base/'evidence.json')},
        'block_closed': bool(closed), 'contract_closed': False, 'source_sha256': digest(path)}
    return {**summarize(row, [capture]), 'block_closed': bool(closed),
            'successor_policy': 'Actual designed entries; root parameters remain fixed',
            'secondary_diagnostics': []}


async def probe_block(row, block, state, options):
    if options.get('designed_successors'):
        return await probe_designed_block(row, block, state, options)
    from mcp import ClientSession, StdioServerParameters
    from mcp.client.stdio import stdio_client
    captures = []
    diagnostic_jobs = []
    command = options['mcp_command']
    env = {**os.environ, 'ROCQ_WORKSPACE': options['workspace'],
           'ROCQ_PET_TIMEOUT': str(options['seconds'])}
    if options.get('feedback_dir'):
        env.update(ZESU_ROCQ_MCP_BINARY=str(HERE/'feedback_mcp.sh'),
                   ZESU_MCP_PYTHON=sys.executable, ZESU_FEEDBACK_DIR=options['feedback_dir'])
    if options.get('complete_dir'):
        env.update(ZESU_ROCQ_MCP_BINARY=str(HERE/'complete_goals_mcp.sh'),
                   ZESU_MCP_PYTHON=sys.executable, ZESU_COMPLETE_GOAL_DIR=options['complete_dir'])
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
                interactive_path = setup_fallback.write_interactive_source(path)
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
                complete_exports = []
                async def export_state(current, label):
                    if not options.get('complete_dir'):
                        return
                    scope = 'post-Abort tooling state; no native discharge claim' if label == 'termination' else 'native checkpoint'
                    if not current.get('success'):
                        complete_exports.append({'success': False, 'checkpoint': label,
                            'coverage': 'unavailable', 'scope': scope,
                            'native_post_call_debts': 'unavailable without a valid successful returned state',
                            'source_sha256': digest(interactive_path), 'source': str(interactive_path.resolve()),
                            'session_directory': options['complete_dir'],
                            'failed_response_sha256': hashlib.sha256(json.dumps(current, sort_keys=True).encode()).hexdigest()})
                        return
                    try:
                        exported = await native_diagnostics.measured_call(session, 'rocq_complete_goals',
                            {'from_state': current['state_id']}, steps, label='capture-' + label)
                        if exported.get('success') and digest(exported['path']) != exported['sha256']:
                            raise ValueError('The complete export hash does not match')
                    except Exception as error:
                        exported = {'success': False, 'error': str(error), 'state_id': current['state_id']}
                    complete_exports.append({**exported, 'checkpoint': label,
                        'coverage': 'complete' if exported.get('success') else 'unavailable', 'scope': scope,
                        'source_sha256': digest(interactive_path), 'source': str(interactive_path.resolve()),
                        'session_directory': options['complete_dir'],
                        'owned_pet_pid': pet_pids[-1] if pet_pids else None})

                load_result = None
                proof_phase_entered = False
                primary_tactic_entered = False
                primary_timeout = False
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
                        'workspace': options['workspace'], 'file': str(interactive_path.resolve()),
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
                    await export_state(opened, 'entry')
                    body = source.split('Proof.\n', 1)[1].split('Abort.', 1)[0]
                    preparation, primary, recorders = native_diagnostics.primary_plan(body)
                    prepared_state = opened
                    if preparation:
                        prepared_state = await native_diagnostics.measured_check(session, prepared_state, preparation,
                            60, steps, 'primary-preparation')
                        calls.append(prepared_state)
                        if not prepared_state.get('success'):
                            raise RuntimeError(prepared_state.get('error', 'Rocq MCP rejected preparation'))
                    await export_state(prepared_state, 'preparation')
                    deadline = time.monotonic() + options['seconds']
                    primary_tactic_entered = True
                    checked = await native_diagnostics.measured_check(session, prepared_state, primary,
                        options['seconds'], steps, 'primary-unchanged-zesu_block')
                    calls.append(checked)
                    primary_timeout = native_diagnostics.is_primary_timeout([checked])
                    await export_state(checked, 'primary')
                    pet_diagnostics.append(data(await session.call_tool('rocq_diag', {})))
                    if not checked.get('success'):
                        raise RuntimeError(checked.get('error', 'Rocq MCP rejected the probe'))
                    if recorders:
                        checked = await native_diagnostics.measured_check(session, checked, recorders,
                            remaining(), steps, 'primary-recorders')
                        calls.append(checked)
                        if not checked.get('success'):
                            raise RuntimeError(checked.get('error', 'Rocq MCP rejected the recorders'))
                    await export_state(checked, 'recorders')
                    tail = await native_diagnostics.measured_check(session, checked,
                        'Abort.' + source.split('Abort.', 1)[1], remaining(), steps,
                        'primary-recorder-termination')
                    calls.append(tail)
                    if not tail.get('success'):
                        raise RuntimeError(tail.get('error', 'Rocq MCP rejected the recorder terminator'))
                    await export_state(tail, 'termination')
                    output = '\n'.join(feedback(value, options.get('feedback_dir')) for value in calls)
                    if checked.get('proof_finished'):
                        output += '\nNo more goals.\n'
                    rc = 0
                except Exception as error:
                    error_text = str(error)
                    output = '\n'.join(feedback(value, options.get('feedback_dir')) for value in calls) + '\n' + str(error)
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
                if primary_timeout and options.get('secondary_enabled', True):
                    diagnostic_jobs.append(path)
                path.with_suffix('.mcp.json').write_text(json.dumps(calls, indent=2) + '\n')
                path.with_suffix('.out').write_text(output)
                records = parse_capture(output, state, block, successor)
                for record in records:
                    record['proof_phase_entered'] = proof_phase_entered
                    if error_text:
                        record['outcome'] = 'mcp-error' if proof_phase_entered else 'setup-error'
                        record['error'] = error_text
                        if primary_timeout:
                            record['outcome'] = 'automation-search-timeout'
                        elif load_result and load_result['outcome'] == 'entry-elaborated':
                            record['outcome'] = 'primary-unavailable'
                    record['setup_path'] = ('coqc-scratch-LOAD/fresh-owned-Pet' if options.get('load_before_start')
                                            else 'coqc-scratch-LOAD') if load_result else 'MCP'
                    record['load_result'] = load_result
                    record['complete_exports'] = [{**value, 'primary_capture_sha256': digest(path.with_suffix('.mcp.json'))} for value in complete_exports]
                    record['complete_native_coverage'] = {'entry', 'preparation', 'primary', 'recorders'} <= {value['checkpoint'] for value in complete_exports} and all(value.get('success') for value in complete_exports if value['checkpoint'] != 'termination')
                    record['complete_group_policy'] = 'Active, stack, shelf, and given-up groups remain separate from primary outcome classification'
                    record['primary_steps'] = steps
                    record['primary_tactic_entered'] = primary_tactic_entered
                    record['primary_invocation_policy'] = 'Preparation receives 60 seconds. The isolated primary receives the configured budget.'
                    record['failed_primary_transaction'] = next((value for value in reversed(calls) if value.get('success') is False), None)
                    record['last_successful_primary_state'] = next((value for value in reversed(calls) if value.get('success')), None)
                    record['contract_closed'] = False
                    record['closure_scope'] = 'abstract successors only'
                    record['pet_diagnostics'] = pet_diagnostics
                    record['pet_peak_mib'] = pet_peak
                    record['rss_uses_unique_processes'] = True
                    record['mcp_health'] = health
                    record['source_sha256'] = digest(path)
                    record['interactive_source'] = str(interactive_path.resolve())
                    record['interactive_source_sha256'] = digest(interactive_path)
                    record['measurement_scope'] = 'worker descendants plus the MCP-reported Pet process; 0.1-second samples and MCP peak measurements'
                    record['elapsed_seconds'] = elapsed
                    record['cpu_seconds'] = max(0, max(sample[1] for sample in samples) - initial_cpu)
                    record['module_limit_seconds'] = options['seconds']
                    record['module_limit_gib'] = 6
                path.with_suffix('.records.json').write_text(json.dumps(records, indent=2) + '\n')
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


def first_native_root(args, parser, workspace):
    """Bind an explicit first native run without creating a comparison baseline."""
    root = args.first_native_run
    if root is None:
        return None
    if not args.designed_successors:
        parser.error('--first-native-run requires --designed-successors')
    for name in ('native_baseline_report', 'native_resume_report', 'resume_report', 'entries'):
        if getattr(args, name):
            parser.error('--first-native-run cannot use --' + name.replace('_', '-'))
    if re.fullmatch(r'[0-9a-f]{40}', root) is None:
        parser.error('--first-native-run requires a full lowercase frozen root SHA')
    actual = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=workspace, text=True).strip()
    if actual != root:
        parser.error('The first native frozen root differs from workspace HEAD')
    return root


TRAINING_LABEL = 'Free training after F42 and F43. The hold-out is spent.'


def verify_training_inputs(root, sources, workspace):
    """Reject a changed root, tracked patch, or retained input before publication."""
    actual = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=workspace, text=True).strip()
    if actual != root:
        raise ValueError('The training root differs from workspace HEAD')
    if subprocess.check_output(['git', 'diff', '--binary', 'HEAD'], cwd=workspace):
        raise ValueError('The training workspace has tracked source changes')
    for name, expected in sources.items():
        path = Path(workspace) / name
        try:
            actual = digest(path)
        except OSError as error:
            raise ValueError('A training input became unavailable: ' + str(name)) from error
        if actual != expected:
            raise ValueError('A training input changed: ' + str(name))


def training_native_root(args, parser, workspace):
    """Bind a fresh training run without a first-run or comparison claim."""
    root = args.training_root
    if root is None:
        return None
    if not args.designed_successors:
        parser.error('--training-root requires --designed-successors')
    for name in ('first_native_run', 'native_baseline_report', 'native_resume_report',
                 'resume_report', 'entries'):
        if getattr(args, name):
            parser.error('--training-root cannot use --' + name.replace('_', '-'))
    if re.fullmatch(r'[0-9a-f]{40}', root) is None:
        parser.error('--training-root requires a full lowercase root SHA')
    if args.out.exists() or args.out.is_symlink():
        parser.error('--training-root requires a nonexistent output path')
    try:
        verify_training_inputs(root, {}, workspace)
    except ValueError as error:
        parser.error(str(error))
    return root


def finish_training_report(report, root, workspace):
    if root is None:
        return
    verify_training_inputs(root, report['inputs'], workspace)
    report.update(label=TRAINING_LABEL, experiment_kind='training', training_root=root,
                  first_native_run=False, measurement_root=root, inputs_unchanged=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--design', type=Path, required=True)
    parser.add_argument('--designed-successors', action='store_true',
                        help='Attempt compiled native proofs with actual successor entries')
    parser.add_argument('--entries', type=Path, help='Use the frozen legacy entry records instead of the design schema')
    parser.add_argument('--trace-import', help='Use this trace module for design-schema entries')
    parser.add_argument('--code-premises', type=Path, help='Read explicit code premises for design-schema entries')
    parser.add_argument('--probe-import', action='append', default=[], help='Import an explicit module in each design-schema probe')
    parser.add_argument('--binding-report', type=Path, help='Require successful source and application validation for design-schema entries')
    parser.add_argument('--cfg', type=Path, required=True)
    parser.add_argument('--manifest', type=Path, required=True)
    parser.add_argument('--out', type=Path, required=True)
    parser.add_argument('--resume-report', type=Path)
    parser.add_argument('--native-resume-report', type=Path)
    parser.add_argument('--native-baseline-report', type=Path)
    parser.add_argument('--first-native-run', metavar='FROZEN_ROOT_SHA',
                        help='Run designed native proofs once at this exact root without a comparison baseline')
    parser.add_argument('--training-root', metavar='TRAINING_ROOT_SHA',
                        help='Run fresh designed native training at this exact root without a first-run or baseline claim')
    parser.add_argument('--terminal', required=True)
    parser.add_argument('--terminal-descriptor', type=Path,
                        help='Read a source-bound owned continuation for designed successor proofs')
    parser.add_argument('--mcp-command', default=str(HERE.parent / 'rocq_mcp_guarded.sh'))
    parser.add_argument('--build-dir', type=Path, default=Path('_build/default').resolve().parent)
    parser.add_argument('--jobs', type=int, default=6)
    parser.add_argument('--seconds', type=int, default=300)
    args = parser.parse_args()
    if not 1 <= args.jobs <= 6 or not 1 <= args.seconds <= 300:
        parser.error('The driver permits one to six workers and at most 300 seconds per MCP call')
    first_root = first_native_root(args, parser, Path.cwd())
    training_root = training_native_root(args, parser, Path.cwd())
    if (args.native_resume_report or args.native_baseline_report) and not args.designed_successors:
        parser.error('Native comparison and reuse require --designed-successors')
    if (args.designed_successors and not args.native_baseline_report
            and first_root is None and training_root is None):
        parser.error('Designed successor proofs require a frozen --native-baseline-report')
    if args.designed_successors and args.entries:
        parser.error('Designed successor proofs require the validated design schema')
    if args.designed_successors and args.resume_report:
        parser.error('Native proof obligations cannot reuse abstract-stop captures')
    if not args.entries and (not args.trace_import or not args.code_premises or not args.binding_report):
        parser.error('Design-schema entries require --trace-import, --code-premises, and --binding-report')
    if args.entries and (args.trace_import or args.code_premises or args.probe_import or args.binding_report):
        parser.error('Legacy entries already contain their probe options')
    if args.terminal_descriptor and not args.designed_successors:
        parser.error('--terminal-descriptor requires --designed-successors')
    training_controls = {}
    if training_root is not None:
        training_controls = {str(path.resolve()): digest(path) for path in (
            args.design, args.cfg, args.manifest, args.binding_report,
            args.code_premises, args.terminal_descriptor) if path is not None}
    terminal_descriptor = (load_terminal_descriptor(args.terminal_descriptor, args.terminal, Path.cwd())
                           if args.terminal_descriptor else None)
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
    if args.designed_successors:
        input_paths.append(HERE/'successor_entailment.py')
    if args.terminal_descriptor:
        input_paths.append(args.terminal_descriptor)
        input_paths.extend(Path(path) for path in terminal_descriptor['source_hashes'])
    if args.native_baseline_report:
        input_paths.append(args.native_baseline_report)
    if args.native_resume_report:
        input_paths.append(args.native_resume_report)
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
    if args.native_baseline_report:
        import successor_entailment
        baseline = json.loads(args.native_baseline_report.read_text())
        for path, expected in baseline['inputs'].items():
            actual = digest(path)
            if actual != expected and Path(path).resolve() not in {
                    Path(__file__).resolve(), (HERE/'complete_goals_mcp.py').resolve()}:
                raise ValueError('A frozen native comparison input changed: ' + path)
            sources[path] = actual
        for row, block, state in ready:
            for target in block['successors'] or [args.terminal]:
                disabled = successor_entailment.native_boundary_source(state, block, design,
                    Path.cwd(), enabled=False, historical_target=chain_root.terminal_target(target),
                    terminal=designed_terminal(block, {'terminal': args.terminal, 'workspace': str(Path.cwd()),
                                                      'terminal_descriptor': terminal_descriptor}))
                expected = next(pair for pair in baseline['pairs'] if pair['entry'] == row['entry_pc']
                                and pair['target'] == target)['sources']['switch-on']
                if hashlib.sha256(disabled['source'].encode()).hexdigest() != expected:
                    raise ValueError('A disabled native source differs from the frozen full-ON baseline')
    if training_root is not None:
        verify_training_inputs(training_root, training_controls, Path.cwd())
        verify_training_inputs(training_root, sources, Path.cwd())
    args.out.mkdir(parents=True, exist_ok=training_root is None)
    options = {'workspace': str(Path.cwd()), 'out': str(args.out.resolve()),
               'mcp_command': args.mcp_command, 'terminal': args.terminal, 'seconds': args.seconds,
               'build_dir': str(args.build_dir.resolve()), 'design': str(args.design.resolve()),
               'designed_successors': args.designed_successors}
    if terminal_descriptor is not None:
        options['terminal_descriptor'] = terminal_descriptor
    reused = []
    if args.native_resume_report:
        previous_native = json.loads(args.native_resume_report.read_text())
        pending = []
        for row, block, state in ready:
            cached = reuse_native_capture(row, block, state, previous_native, options)
            if cached:
                reused.append(cached)
            else:
                pending.append((row, block, state))
        ready = pending
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
    report = {'schema': 1, 'label': ('Phase 1 I1 native designed-boundary discovery' if args.designed_successors else
                                   'Phase 1 WP5 designed-entry discovery; no proof completion claim'),
              'measurement_root': baseline['root_commit'] if args.native_baseline_report else first_root,
              'capture_only': not args.designed_successors,
              'designed_successors': args.designed_successors,
              'frozen_baseline_report': str(args.native_baseline_report) if args.native_baseline_report else None,
              'blocks_closed': sum(bool(record.get('block_closed')) for record in records),
              'contract_closures': 0, 'probe_imports': args.probe_import, 'artifact_identity': manifest['artifact_identity'],
              'selected_elf_sha256': manifest['elf_sha256'], 'inputs': sources, 'block_count': len(design['blocks']),
              'workers': args.jobs, 'new_block_runs': len(ready), 'reused_block_runs': len(reused),
              'elapsed_seconds': elapsed,
              'resumed_capture_run_seconds': previous['elapsed_seconds'] if args.resume_report else None,
              'peak_worker_mib_upper_bound': max((value['peak_mib'] for value in measurements), default=None),
              'peak_pet_mib': max((capture.get('pet_peak_mib') or 0 for row in records for capture in row['captures']), default=None),
              'machine_before': before, 'machine_after': machine(),
              'classes': dict(Counter(value for row in records for value in row['outcomes'])),
              'blocks': sorted(records, key=lambda row: gen_block.address(row['entry']))}
    if first_root is not None:
        actual = subprocess.check_output(['git', 'rev-parse', 'HEAD'], text=True).strip()
        if actual != first_root:
            raise ValueError('The first native frozen root changed during execution')
        report['first_native_run'] = True
    finish_training_report(report, training_root, Path.cwd())
    chain_root.atomic_json(args.out / 'report.json', report)
    print(json.dumps({'report': str(args.out / 'report.json'), 'sha256': digest(args.out / 'report.json'),
                      'classes': report['classes'], 'elapsed_seconds': elapsed}))
    return 1 if any(report['classes'].get(key) for key in ('error', 'setup-error', 'mcp-error', 'primary-unavailable', 'automation-search-timeout')) else 0


if __name__ == '__main__':
    raise SystemExit(main())
