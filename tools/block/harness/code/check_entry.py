#!/usr/bin/env python3
"""Check one inline entry with two fixed native proofs. Keep truth private."""

import argparse
from copy import deepcopy
from contextlib import chdir
import fcntl
import hashlib
import importlib.util
import json
import math
import os
from pathlib import Path
import re
import signal
import subprocess
import sys
import tempfile
import time
import traceback

from entry_pilot import CpuLedger, SOURCE_COMMIT, budget, copy_bound, relative, retain_residual
from entry_pilot_checker import bound_json, install_inline, native_result, strict_loads, validate_inline


ROOT = Path(__file__).resolve().parents[4]
CGROUP_ROOT = Path('/sys/fs/cgroup')
PUBLIC_LIMIT = 6144


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def atomic_json(path, value):
    path = Path(path)
    fd, temporary = tempfile.mkstemp(prefix='.check-entry-', dir=path.parent)
    try:
        with os.fdopen(fd, 'w') as output:
            json.dump(value, output, ensure_ascii=False, indent=2, allow_nan=False)
            output.write('\n')
            output.flush()
            os.fsync(output.fileno())
        os.replace(temporary, path)
    finally:
        if os.path.exists(temporary):
            os.unlink(temporary)


def bound_rows(rows):
    paths = set()
    for row in rows:
        path = Path(row['path']).resolve()
        if path in paths or digest(path) != row['sha256']:
            raise ValueError('A runtime binding changed or repeats.')
        paths.add(path)


def source_statement(path):
    """Keep the original header, statement, and sole native proof body."""
    sys.path.insert(0, str(ROOT/'tools'))
    from residual.modules import parse_module
    proofs = [row for row in parse_module(Path(path)) if row.name.startswith('DesignedBoundary_')]
    if len(proofs) != 1 or proofs[0].inline:
        raise ValueError('The native source needs one separate boundary proof.')
    proof = proofs[0]
    if ''.join(proof.body).strip() != 'zesu_block.':
        raise ValueError('The original native proof has another body.')
    lines = Path(path).read_text().splitlines(keepends=True)
    return {'name': proof.name, 'prefix': ''.join(lines[:proof.declaration_line]),
            'statement': ''.join(lines[proof.declaration_line:proof.proof_line]),
            'native_body': 'zesu_block.'}


def case_plan(cases, measurements, workspace=ROOT):
    """Bind 19 pairs to the selected measured source boundary."""
    sys.path.insert(0, str(ROOT/'tools/block'))
    from scratch_block import find_block
    if cases['parent'] != SOURCE_COMMIT or len(cases['cases']) != 19:
        raise ValueError('The case set has another boundary or size.')
    measured = {row['module'].split('.')[-1]: row for row in measurements['rows']}
    result = []
    for case in cases['cases']:
        if not case['eligible'] or any(case['natural_cut_flags'].values()) or len(case['predecessor_blocks']) != 1:
            raise ValueError('The primary case changes the reviewed boundary.')
        row = {'case': deepcopy(case)}
        for side, pc in [('predecessor', case['predecessor_blocks'][0]), ('successor', case['target_pc'])]:
            source = find_block(workspace, pc)
            measurement = measured[source.stem]
            specification = source_statement(source)
            receipt = bound_json(measurement['result']['path'], measurement['result']['sha256'])
            if receipt['source_sha256'] != digest(source) or receipt['assumptions'] != [] or receipt['module_m'] is not True:
                raise ValueError('A measurement does not match the current native source or exact acceptance.')
            obj = receipt['object']
            if digest(obj['path']) != obj['sha256']:
                raise ValueError('The accepted measurement object changed.')
            row[side] = {'source': str(source.relative_to(workspace)), 'source_sha256': digest(source),
                         'module': '.'.join(source.relative_to(workspace).with_suffix('').parts),
                         'theorem': specification['name'],
                         'statement': specification['statement'],
                         'statement_sha256': hashlib.sha256(specification['statement'].encode()).hexdigest(),
                         'cpu_seconds': measurement['cpu_seconds'],
                         'peak_bytes': measurement['peak_rss_kib']*1024,
                         'measurement_binding': deepcopy(measurement['result'])}
        row['cpu_budget_seconds'] = budget(row)
        result.append(row)
    return result


def affected_order(edges, changed, targets):
    """Rebuild changed ancestors of the two native targets in dependency order."""
    dependencies, reverse = {}, {}
    for edge in edges:
        dependencies.setdefault(edge['from'], set()).add(edge['to'])
        reverse.setdefault(edge['to'], set()).add(edge['from'])
    def closure(seeds, graph):
        found, pending = set(seeds), list(seeds)
        while pending:
            for name in graph.get(pending.pop(), ()):
                if name not in found:
                    found.add(name)
                    pending.append(name)
        return found
    required = closure(changed, reverse) & closure(targets, dependencies)
    required.update(targets)
    ordered, visiting, done = [], set(), set()
    def visit(name):
        if name in done:
            return
        if name in visiting:
            raise ValueError('The import graph contains a cycle.')
        visiting.add(name)
        for child in sorted(dependencies.get(name, set()) & required):
            visit(child)
        visiting.remove(name)
        done.add(name)
        ordered.append(name)
    for name in sorted(required):
        visit(name)
    return ordered


class AnswerRefused(ValueError):
    """A selected candidate failed compact expansion in the renderer."""
    def __init__(self, error, origin):
        super().__init__(str(error))
        self.origin = origin


COMPACT_ANSWER_OPERATIONS = frozenset({
    'compact_record', 'compact_identifier', 'compact_reference', '_compact_expand',
    '_compact_body_symbols', '_compact_entry_binders', '_compact_anchor',
    '_compact_continuation', '_compact_introduction', '_compact_body_fields',
    '_compact_row_annotations'})


def compact_answer_origin(error, generator, candidate_pc):
    """Require both a renderer operation and the selected candidate body."""
    frames = []
    trace = error.__traceback__
    while trace is not None:
        frames.append(trace.tb_frame)
        trace = trace.tb_next
    if not frames or candidate_pc is None:
        return None
    generator = Path(generator).resolve()
    last = frames[-1]
    operation = last.f_code.co_qualname
    if (Path(last.f_code.co_filename).resolve() != generator or
            not (last.f_code.co_name in COMPACT_ANSWER_OPERATIONS or
                 operation.startswith('_compact_typed_author.<locals>.'))):
        return None
    for frame in frames:
        if Path(frame.f_code.co_filename).resolve() != generator:
            continue
        for name in ('body', 'value'):
            body = frame.f_locals.get(name)
            if isinstance(body, dict) and body.get('at') == candidate_pc:
                return {'operation': operation, 'exception_type': 'ValueError'}
    return None


def answer_error_feedback(message):
    """Bound the encoded renderer text. Keep the complete message private."""
    text = str(message)
    while len(json.dumps(text, ensure_ascii=False).encode('utf-8')) > 2048:
        text = text[:len(text)//2]
    return text


def read_answer_refusal(output, row):
    path = Path(output)/'ANSWER-REFUSAL.json'
    if not path.exists():
        return None
    try:
        value = strict_loads(path.read_text())
        if (value.get('schema') != 'entry-pilot.answer-refusal.v1' or
                value.get('phase') != 'compact_expansion' or
                value.get('case_id') != row['case']['case_id'] or
                value.get('target_pc') != row['case']['target_pc'] or
                not isinstance(value.get('message'), str) or
                value.get('origin', {}).get('exception_type') != 'ValueError'):
            return None
        return value
    except (OSError, ValueError, AttributeError):
        return None


def construct(author, workspace, portable, *, candidate_pc=None):
    """Use the existing producer. Do not compare against hidden truth."""
    with chdir(workspace):
        generator_path = workspace/'ZesuSsz/Evidence/generate_block_design.py'
        specification = importlib.util.spec_from_file_location('check_entry_design', generator_path)
        module = importlib.util.module_from_spec(specification)
        specification.loader.exec_module(module)
        inventory = strict_loads((workspace/'build/stock-zisk/inventory.json').read_text())
        read = lambda name: strict_loads((portable/name).read_text())
        source_closure = read('GLOBAL-SOURCE-CLOSURE.json')
        notation_choices = read('NOTATION-CHOICES.json')
        registry_evidence = read('REGISTRY-EVIDENCE.json')
        try:
            profile = module.construct_profile(inventory, 'decodeItem', author, root=workspace,
                source_closure=source_closure, notation_choices=notation_choices,
                registry_evidence=registry_evidence)
        except ValueError as error:
            origin = compact_answer_origin(error, generator_path, candidate_pc)
            if origin is None:
                raise
            raise AnswerRefused(error, origin) from error
        design = module.build(inventory, 'decodeItem', profile, root=workspace, generator=generator_path)
        from render_support import render_support
        outputs = render_support(design, workspace, name_prefix='decodeItem')
        return profile, design, outputs


def materialize(runtime, row, response, output):
    """Copy bound inputs and replace exactly one inline author body."""
    source = output/'workspace'
    source.mkdir()
    copies = []
    for binding in runtime['copies']:
        target = source/relative(binding['relative_path'])
        copied = copy_bound(binding['source'], target, binding['sha256'])
        target.chmod(binding['mode'])
        copied['mode'] = binding['mode']
        copies.append(copied)
    for directory in runtime.get('empty_dirs', []):
        (source/relative(directory)).mkdir(parents=True, exist_ok=True)
    for link in runtime.get('source_links', []):
        target = source/relative(link['relative_path'])
        resolved = (target.parent/link['target']).resolve()
        if not resolved.is_relative_to(source.resolve()) or not resolved.exists():
            raise ValueError('An import alias leaves its owned workspace or is absent.')
        target.parent.mkdir(parents=True, exist_ok=True)
        target.symlink_to(link['target'], target_is_directory=resolved.is_dir())
    author_path = source/relative(runtime['author_path'])
    author = strict_loads(author_path.read_text())
    author = install_inline(author, row['case'], response)
    author_path.write_text(json.dumps(author, indent=2)+'\n')
    for binding in runtime['relocations']:
        target = source/relative(binding['relative_path'])
        if digest(target) != binding['source_sha256']:
            raise ValueError('A runtime relocation has another input.')
        text = target.read_text()
        for old, new in binding['replacements']:
            text = text.replace(old, str(source)+new)
        target.write_text(text)
    atomic_json(output/'INPUT-COPIES.json', copies)
    return source


def produce(runtime, row, workspace, output):
    author = strict_loads((workspace/relative(runtime['author_path'])).read_text())
    try:
        profile, design, outputs = construct(author, workspace, workspace/relative(runtime['portable_path']),
                                            candidate_pc=row['case']['target_pc'])
    except AnswerRefused as error:
        atomic_json(output/'ANSWER-REFUSAL.json', {'schema': 'entry-pilot.answer-refusal.v1',
            'phase': 'compact_expansion', 'case_id': row['case']['case_id'],
            'target_pc': row['case']['target_pc'], 'message': str(error), 'origin': error.origin})
        raise
    if {str(name) for name in outputs} != set(runtime['generated_outputs']):
        raise ValueError('The producer changed its output set.')
    changed = []
    for name, text in outputs.items():
        path = workspace/relative(name)
        if not path.exists() or path.read_text() != text:
            changed.append('.'.join(Path(name).with_suffix('').parts))
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text)
        module = '.'.join(Path(name).with_suffix('').parts)
        physical = workspace/relative(runtime['module_files'][module])
        physical.parent.mkdir(parents=True, exist_ok=True)
        physical.write_text(text)
    atomic_json(output/'PROFILE.json', profile)
    atomic_json(output/'DESIGN.json', design)
    targets = [row[side]['module'] for side in ('predecessor', 'successor')]
    ordered = affected_order(runtime['import_edges'], changed, targets)
    module_files = runtime['module_files']
    for name in ordered:
        path = workspace/relative(module_files[name])
        for suffix in ('.vo', '.vos', '.vok', '.glob'):
            path.with_suffix(suffix).unlink(missing_ok=True)
        (path.parent/('.'+path.stem+'.aux')).unlink(missing_ok=True)
    for side in ('predecessor', 'successor'):
        source = workspace/relative(runtime['module_files'][row[side]['module']])
        if digest(source) != row[side]['source_sha256']:
            raise ValueError('The attempt changed a native source or its public statement.')
    atomic_json(output/'INVALIDATION.json', {'changed_generated_modules': changed, 'ordered': ordered,
        'native_targets': targets, 'native_sources_unchanged': True})
    return ordered


def aggregate_root(environment=os.environ, proc=Path('/proc'), root=CGROUP_ROOT):
    name = environment.get('ZESU_AGGREGATE_SLICE', '')
    if not environment.get('ZESU_IN_BATCH') or not re.fullmatch(r'zesuaggregate[0-9]+p[0-9]+r[0-9]+\.slice', name):
        raise ValueError('Execution requires one fresh stock batch per attempt.')
    membership = next(line[3:] for line in (proc/'self/cgroup').read_text().splitlines() if line.startswith('0::'))
    parts = Path(membership).parts
    if parts.count(name) != 1:
        raise ValueError('The attempt does not belong to its stock aggregate.')
    selected = root/Path(*parts[1:parts.index(name)+1])
    if not (selected/'cpu.stat').is_file():
        raise ValueError('The stock aggregate has no CPU counter.')
    return selected


class BudgetExceeded(RuntimeError):
    pass


def run_phase(argv, cwd, environment, output, ledger, *, popen=subprocess.Popen, pause=time.sleep):
    """Sample only local aggregate CPU. Stock batch cleanup owns remaining scopes."""
    with (output.with_suffix('.stdout')).open('wb') as stdout, (output.with_suffix('.stderr')).open('wb') as stderr:
        child = popen(argv, cwd=cwd, env=environment, stdout=stdout, stderr=stderr, start_new_session=True)
        try:
            while child.poll() is None:
                sample = ledger.read()
                if sample['budget_exceeded']:
                    atomic_json(output.with_suffix('.budget.json'), sample)
                    raise BudgetExceeded('The aggregate CPU budget ended.')
                pause(.25)
            code = child.wait()
            sample = ledger.read()
            atomic_json(output.with_suffix('.cpu.json'), sample)
            if sample['budget_exceeded']:
                raise BudgetExceeded('The aggregate CPU budget ended.')
            if code:
                raise RuntimeError('A stock phase failed.')
            return sample
        finally:
            if child.poll() is None:
                os.killpg(child.pid, signal.SIGTERM)
                try:
                    child.wait(timeout=2)
                except subprocess.TimeoutExpired:
                    os.killpg(child.pid, signal.SIGKILL)
                    child.wait()


def public_result(case_id, status, reason, cpu_seconds, budget_seconds):
    value = {'schema': 'entry-pilot.feedback.v1', 'case_id': case_id, 'status': status,
             'primary_success': status == 'pass', 'reason': reason,
             'cpu_seconds': cpu_seconds, 'cpu_budget_seconds': budget_seconds,
             'separate_equivalence_proof': False}
    if len(json.dumps(value, ensure_ascii=False).encode()) > PUBLIC_LIMIT:
        raise ValueError('The public feedback exceeds six KiB.')
    return value


def attempt_identity(row, response):
    """Keep candidate and edge identities in private receipts only."""
    encoded = json.dumps(response, sort_keys=True, separators=(',', ':'), ensure_ascii=False).encode()
    return {'case_id': row['case']['case_id'], 'candidate_sha256': hashlib.sha256(encoded).hexdigest(),
            'edge': {'predecessor_pc': row['case']['predecessor_blocks'][0],
                     'successor_pc': row['case']['target_pc']},
            'exact_statements': {side: {'module': row[side]['module'],
                'theorem': row[side]['theorem'], 'statement': row[side]['statement'],
                'statement_sha256': row[side]['statement_sha256']}
                for side in ('predecessor', 'successor')}}


def failure_classification(progress):
    """Name the failed proof side without asserting its semantic cause."""
    side, phase = progress.get('side'), progress.get('phase')
    if phase == 'native_search' and side in ('predecessor', 'successor'):
        return side + '_native_search_failed'
    return 'producer_or_runtime_failed'


def require_truth_gate(gate, case_ids, selected_case=None):
    """Require each released truth case and both native negatives."""
    if gate.get('Root_accepted') is not True or gate.get('source_commit') != SOURCE_COMMIT:
        raise ValueError('The complete truth gate lacks Root acceptance.')
    passed = set(gate['passed_case_ids'])
    if len(passed) != len(gate['passed_case_ids']):
        raise ValueError('The truth gate repeats a case.')
    if gate.get('per_case_release') is True:
        if not passed or not passed <= set(case_ids):
            raise ValueError('The truth gate names an unknown or empty case set.')
    elif passed != set(case_ids):
        raise ValueError('The truth gate does not cover all primary cases.')
    if selected_case is not None and selected_case not in passed:
        raise ValueError('The selected case lacks its accepted truth control.')
    expected = {'unsupported-strengthening': 'predecessor_native_search_failed',
                'unsupported-weakening': 'successor_native_search_failed'}
    controls = gate.get('negative_controls', {})
    if set(controls) != set(expected):
        raise ValueError('The truth gate lacks both native negative controls.')
    for label, failure in expected.items():
        binding = controls[label]
        result = bound_json(binding['result']['path'], binding['result']['sha256'])
        acceptance = bound_json(binding['Root_acceptance']['path'], binding['Root_acceptance']['sha256'])
        if (acceptance.get('accepted') is not True
                or acceptance.get('result_sha256') != binding['result']['sha256']
                or result.get('negative_control_label') != label
                or result.get('negative_control_passed') is not True
                or result.get('primary_success') is not False
                or result.get('failure_classification') != failure):
            raise ValueError('A native negative control lacks exact Root acceptance.')


def admission_status(runtime, *, available=None):
    """Check a preassigned Root claim. Never change or release the ledger."""
    from admission_memory import projection, guard_lock
    policy = runtime['canonical_admission']
    sys.path.insert(0, policy['reviewed_helpers'])
    from claims import active_claims
    from io_helpers import memory_available
    with guard_lock(), Path(policy['lock']).open('a') as lock:
        fcntl.flock(lock, fcntl.LOCK_EX)
        data = strict_loads(Path(policy['ledger']).read_text())
        assigned = data['fixed_claims'].get(policy['claim_key'], 0)
        if type(assigned) is not int or assigned < policy['minimum_claim_bytes']:
            raise ValueError('The attempt lacks its Root-assigned canonical claim.')
        claims = active_claims(data, policy['legacy_release_bindings'])
        free = memory_available() if available is None else available()
        total = sum(claims.values())
        return {'time_ns': time.time_ns(), 'claim_key': policy['claim_key'],
                'assigned_bytes': assigned, 'active_claim_bytes': total,
                'capture_headroom_bytes': policy['capture_headroom_bytes'],
                'MemAvailable_bytes': free, 'budget_bytes': free * 7 // 10,
                **projection(data, claims, policy['capture_headroom_bytes'], free),
                'ledger_sha256': digest(policy['ledger']), 'ledger_changed': False}


def wait_admission(runtime, output, *, pause=time.sleep):
    records = []
    while True:
        bound_rows(runtime['bindings'])
        record = admission_status(runtime)
        records.append(record)
        atomic_json(output/'ADMISSION.json', records)
        if record['admitted']:
            return record
        pause(60)


def require_attempt_release(admission, case_id, response_sha256, output):
    if (admission.get('case_id') != case_id
            or admission.get('response_sha256') != response_sha256
            or admission.get('output_path') != str(Path(output).resolve())
            or not isinstance(admission.get('claim_key'), str) or not admission['claim_key']):
        raise ValueError('The released runtime does not bind this single attempt and claim.')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('response', type=Path)
    parser.add_argument('--runtime', required=True, type=Path)
    parser.add_argument('--runtime-sha256', required=True)
    parser.add_argument('--output', required=True, type=Path)
    parser.add_argument('--execute', action='store_true')
    args = parser.parse_args()
    if not args.output.resolve().is_relative_to(ROOT/'_build'):
        parser.error('The private attempt output must stay in the owned worktree build directory.')
    args.output.mkdir(parents=True, exist_ok=False, mode=0o700)
    try:
        return run_attempt(args)
    except BaseException as error:
        if not (args.output/'RESULT.json').exists():
            atomic_json(args.output/'RESULT.json', {'private': True, 'primary_success': False,
                'reason': 'checker_setup_or_accounting_error', 'private_error': traceback.format_exc(),
                'Root_acceptance_required': True})
            print(json.dumps({'schema': 'entry-pilot.feedback.v1', 'status': 'fail',
                'primary_success': False, 'reason': 'checker_setup_or_accounting_error'}))
        if isinstance(error, KeyboardInterrupt):
            raise
        raise SystemExit(1)


def run_attempt(args):
    runtime = bound_json(args.runtime, args.runtime_sha256)
    if runtime['source_commit'] != SOURCE_COMMIT:
        raise ValueError('The checker requires exact eea6cadd.')
    bound_rows(runtime['bindings'])
    response = strict_loads(args.response.read_text())
    rows = [row for row in runtime['cases'] if row['case']['case_id'] == response.get('case_id')]
    if len(rows) != 1:
        raise ValueError('The response does not name one primary case.')
    row = rows[0]
    validate_inline(response, row['case'])
    if runtime.get('mode') == 'hidden_truth_control' and digest(args.response) != row['truth_control_response']['sha256']:
        raise ValueError('The truth runtime requires its exact private control response.')
    if runtime.get('mode') == 'negative_control':
        matches = [control for control in runtime['negative_controls']
                   if control['case_id'] == response['case_id'] and control['sha256'] == digest(args.response)]
        if len(matches) != 1:
            raise ValueError('The negative runtime requires its exact private control input.')
    if runtime.get('mode') not in ('hidden_truth_control', 'candidate', 'negative_control'):
        raise ValueError('The checker mode is unsupported.')
    if runtime.get('mode') == 'candidate':
        gate = bound_json(runtime['truth_gate']['path'], runtime['truth_gate']['sha256'])
        require_truth_gate(gate, {item['case']['case_id'] for item in runtime['cases']}, row['case']['case_id'])
    if not args.execute:
        atomic_json(args.output/'PREPARED.json', {'case_id': row['case']['case_id'],
            'runtime_sha256': args.runtime_sha256, 'response_sha256': digest(args.response),
            'cpu_budget_seconds': budget(row), 'execution_released': False})
        print(json.dumps({'status': 'prepared', 'case_id': row['case']['case_id']}))
        return
    if runtime.get('execution_released') is not True:
        raise ValueError('Root did not release this exact checker runtime.')
    admission = runtime['canonical_admission']
    require_attempt_release(admission, row['case']['case_id'], digest(args.response), args.output)
    # All CPU after this point belongs to this single attempt aggregate.
    ledger = CpuLedger([aggregate_root()], budget(row))
    result = {'case_id': row['case']['case_id'], 'primary_success': False,
              'source_commit': SOURCE_COMMIT, 'native_receipts': {}, 'private': True,
              'identity': attempt_identity(row, response)}
    reason = 'checker_error'
    try:
        ledger.read()
        wait_admission(runtime, args.output)
        workspace = materialize(runtime, row, response, args.output)
        request = {'runtime': str(args.runtime.resolve()), 'runtime_sha256': args.runtime_sha256,
                   'case_id': row['case']['case_id'], 'workspace': str(workspace), 'output': str(args.output),
                   'cpu_budget_seconds': budget(row), 'identity': result['identity']}
        atomic_json(args.output/'REQUEST.json', request)
        # The producer and proof worker run inside the same stock aggregate.
        command = [runtime['python'], runtime['proof_worker'], str(args.output/'REQUEST.json')]
        run_phase(command, workspace, dict(os.environ), args.output/'stock-worker', ledger)
        result['native_receipts'] = strict_loads((args.output/'NATIVE-RESULTS.json').read_text())
        expected = {side: row[side]['statement_sha256'] for side in ('predecessor', 'successor')}
        if strict_loads((args.output/'TRANSPORT-CLOSED.json').read_text()).get('normal_context_exit') is not True:
            raise ValueError('The proof transport did not close normally.')
        result['primary_success'] = native_result(result['native_receipts'], expected)
        reason = 'both_exact_native_proofs_pass' if result['primary_success'] else 'native_proof_failed'
    except BudgetExceeded:
        reason = 'aggregate_cpu_budget'
    except BaseException:
        result['private_error'] = traceback.format_exc()
        refusal = read_answer_refusal(args.output, row)
        if refusal is not None:
            reason = 'answer_refused'
            result['answer_error'] = refusal['message']
    finally:
        for name, key in [('NATIVE-RESULTS.json', 'native_receipts'), ('PROGRESS.json', 'last_progress')]:
            path = args.output/name
            if path.exists():
                result[key] = strict_loads(path.read_text())
        result['failure_classification'] = (None if result['primary_success'] else
            'answer_refused' if reason == 'answer_refused' else
            failure_classification(result.get('last_progress', {})))
        residual = args.output/'first-residual/RESIDUAL.json'
        if residual.exists():
            index = strict_loads((residual.parent/'PRIVATE-INDEX.json').read_text())
            result['retained_goal_state'] = {'path': str(residual.resolve()), 'sha256': digest(residual),
                'state_source': index['state_source'], 'qualifier': index['qualifier'], 'agent_visible': False}
        sample = ledger.read()
        if sample['budget_exceeded']:
            result['primary_success'] = False
            reason = 'aggregate_cpu_budget'
        result.update(cpu=sample, cpu_budget_seconds=budget(row), reason=reason,
                      runtime_sha256=args.runtime_sha256, response_sha256=digest(args.response),
                      stock_batch_cleanup_required=True)
        if runtime.get('mode') == 'negative_control':
            result['negative_control_label'] = matches[0]['label']
            expected_failure = matches[0]['expected_failure_classification']
            predecessor_passed = 'predecessor' in result['native_receipts']
            result['negative_control_passed'] = (not result['primary_success']
                and result['failure_classification'] == expected_failure
                and reason != 'aggregate_cpu_budget'
                and 'retained_goal_state' in result
                and (expected_failure != 'successor_native_search_failed' or predecessor_passed)
                and not any(item.get('result', {}).get('pet_restarted') or item.get('result', {}).get('restarted') for item in
                    strict_loads((args.output/'CALLS.json').read_text())))
        # This is the single private result for the attempt. Raw files remain private.
        atomic_json(args.output/'RESULT.json', result)
        feedback = public_result(row['case']['case_id'], 'pass' if result['primary_success'] else 'fail',
                                 reason, sample['cpu_seconds'], budget(row))
        if reason == 'answer_refused':
            feedback['answer_error'] = answer_error_feedback(result['answer_error'])
        print(json.dumps(feedback, ensure_ascii=False))
    if not result['primary_success'] and not result.get('negative_control_passed'):
        raise SystemExit(1)


if __name__ == '__main__':
    main()
