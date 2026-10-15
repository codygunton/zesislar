"""Join filtered proof closure to the accepted operation in its owned session."""

import json
from pathlib import Path

from trace_block_seal import checked_reference
from trace_block_chunks import MAX_RECORD_BYTES


def _owned(reference, root):
    path = checked_reference(reference)
    if not path.resolve(strict=True).is_relative_to(root):
        raise ValueError('The proof operation evidence leaves its owned session directory.')
    if path.stat().st_size > MAX_RECORD_BYTES:
        raise ValueError('A filtered proof operation exceeds the serialized record byte limit.')
    return path


def _result(operation, root):
    response = json.loads(_owned(operation, root).read_text())
    result = response.get('structuredContent')
    if response.get('isError') is True or not isinstance(result, dict) or result.get('success') is not True:
        raise ValueError('A session proof operation has no successful MCP response.')
    return result


def verify_kernel_closure(session, request, *, evidence_dir):
    """Require accepted Qed on the exact retained source-state chain."""
    closure = session.get('closure_check')
    if closure is None:
        return None
    root = Path(evidence_dir).resolve(strict=True)
    if (not isinstance(closure, dict) or closure.get('command') != 'Qed.'
            or closure.get('accepted') is not True or closure.get('unresolved_evars') is not False):
        raise ValueError('The filtered closure lacks an accepted Qed record.')
    reference = closure.get('operation')
    if not isinstance(reference, dict) or set(reference) != {'path', 'sha256'}:
        raise ValueError('The filtered closure lacks its exact Qed operation reference.')
    record = session.get('final_obligations', {})
    if record.get('evidence') != reference:
        raise ValueError('Final obligations differ from the accepted Qed operation.')
    counts = record.get('counts')
    if (record.get('availability') != 'complete' or record.get('method') != 'kernel-accepted-Qed'
            or not isinstance(counts, dict) or set(counts) != {'goals', 'stack', 'shelf', 'given_up'}
            or any(type(value) is not int or value != 0 for value in counts.values())
            or type(record.get('undefined_evars')) is not int or record['undefined_evars'] != 0):
        raise ValueError('The accepted Qed lacks its exact empty final-obligation record.')
    operations = session.get('operations')
    if not isinstance(operations, list):
        raise ValueError('The filtered session lacks its proof operation list.')
    starts = [operation for operation in operations if operation.get('tool') == 'rocq_trace_start']
    if len(starts) != 1:
        raise ValueError('The filtered closure requires one exact proof start.')
    start = starts[0]
    expected = {'workspace': request.get('workspace'), 'file': request.get('source'), 'theorem': request.get('theorem')}
    if not all(expected.values()) or start.get('arguments') != expected:
        raise ValueError('The filtered proof start differs from the prepared source.')
    matches = [operation for operation in operations
               if {key: operation.get(key) for key in reference} == reference]
    if len(matches) != 1:
        raise ValueError('The Qed reference is not one exact same-session operation.')
    target = matches[0]
    if target.get('tool') != 'rocq_trace_run':
        raise ValueError('The closure reference is not a proof command operation.')
    state = None
    closed = False
    for operation in operations:
        if operation is start:
            result = _result(operation, root)
            if result.get('file') != request['source'] or result.get('theorem') != request['theorem']:
                raise ValueError('The accepted proof start differs from the prepared declaration.')
            state = result.get('state_id')
            if type(state) is not int or state < 0:
                raise ValueError('The proof start lacks its exact source-state identity.')
        elif operation.get('tool') == 'rocq_trace_run':
            if state is None or closed:
                raise ValueError('A proof command lies outside the accepted proof-state chain.')
            arguments = operation.get('arguments', {})
            if arguments.get('from_state') != state or type(arguments.get('from_state')) is not int:
                raise ValueError('A proof command has a different source-state identity.')
            if type(arguments.get('trial')) is not bool:
                raise ValueError('A proof command lacks exact trial attribution.')
            result = _result(operation, root)
            if type(result.get('accepted')) is not bool or type(result.get('state_id')) is not int:
                raise ValueError('A proof command lacks its exact accepted-state result.')
            if operation is target:
                if arguments.get('command') != 'Qed.' or arguments['trial'] is not False or result['accepted'] is not True:
                    raise ValueError('The closure operation is not accepted native Qed.')
                evidence = {key: result.get(key) for key in ('path', 'sha256')}
                retained = json.loads(_owned(evidence, root).read_text())
                state_check = retained.get('retained_state_check', {})
                if (retained.get('accepted') is not True or retained.get('retained_state_hash_unchanged') is not True
                        or not isinstance(state_check, dict) or state_check.get('method') != 'Pet.state_hash'
                        or type(state_check.get('before')) is not int or type(state_check.get('after')) is not int
                        or state_check['before'] != state_check['after']):
                    raise ValueError('The retained Qed result lacks acceptance or public state-hash equality.')
                closed = True
            if result['accepted'] and arguments['trial'] is False:
                if result['state_id'] == state:
                    raise ValueError('An accepted native operation did not advance its state identity.')
                state = result['state_id']
            elif result['state_id'] != state:
                raise ValueError('A discarded or refused operation changed its retained state identity.')
    if not closed:
        raise ValueError('The session never reached its exact accepted Qed operation.')
    if type(session.get('final_state_id')) is not int or session['final_state_id'] != state:
        raise ValueError('The accepted Qed result differs from the final session state identity.')
    return reference
