"""Bind filtered classifications to exact schema2 counter and capture files."""

import hashlib
import json
from pathlib import Path

from trace_block_chunks import MAX_RECORD_BYTES
from trace_block_filtered import guard_manifest
from trace_block_filtered_events import FilteredEvents


def filtered_index_rows(events):
    """Derive ordered index rows from verified native event bytes."""
    attempted, captured = [], []
    for reference in events.references:
        row = events.read(reference)
        if row['kind'] == 'guard-counter':
            client = row['client']
            descriptor = events.counters.descriptors[client]
            decision = row['classification']
            if row.get('guard_hash') != descriptor['typed_guard']['sha256']:
                decision = 'unknown'
            attempted.append({'rule': descriptor['rule'], 'client': client,
                              'invocation': row['invocation'], 'classification': decision,
                              'guard_hash': row.get('guard_hash'), 'event': dict(reference)})
        elif row['kind'] == 'native-entry' and row.get('trial') is False:
            captured.append({'rule': events.counters.descriptors[row['rule']]['rule'],
                             'client': row['rule'], 'invocation': row['invocation'],
                             'event': dict(reference)})
    return attempted, captured


def verify_filtered_index(raw, request, index, trace, process):
    """Verify every guard and its exact capture before crediting coverage.

    The caller must bind the complete owned event set and the raw root seal.
    This function rechecks every referenced schema2 envelope and logical capture.
    """
    if index.get('selection_policy') != 'source-filtered-v1' or index.get('schema') != 2:
        raise ValueError('The filtered raw index has an unsupported policy.')
    descriptors = request['entry_descriptors']
    if 'selected_rules' in request:
        selected = request['selected_rules']
    else:
        assignments = request.get('rule_set')
        if (not isinstance(assignments, list) or any(not isinstance(row, dict)
                or not isinstance(row.get('name'), str) or type(row.get('enabled')) is not bool
                for row in assignments)):
            raise ValueError('The sealed request lacks exact switch assignments.')
        selected = [row['name'] for row in assignments]
    if (not isinstance(selected, list) or any(not isinstance(name, str) or not name for name in selected)
            or len(selected) != len(set(selected))):
        raise ValueError('The filtered selected-rule list is invalid.')
    if set(selected) != {row['rule'] for row in descriptors.values()}:
        raise ValueError('The filtered descriptors differ from the selected rules.')
    if index.get('guard_manifest') != request.get('guard_manifest'):
        raise ValueError('The raw index has a different guard manifest binding.')
    manifest = request.get('guard_manifest', {})
    with Path(manifest['path']).open('rb') as stream:
        payload = stream.read(MAX_RECORD_BYTES + 1)
    if (len(payload) > MAX_RECORD_BYTES or hashlib.sha256(payload).hexdigest() != manifest.get('sha256')
            or json.loads(payload) != guard_manifest(descriptors)[0]):
        raise ValueError('The filtered guard manifest differs from the source-bound descriptors.')
    events = FilteredEvents(raw, index['events'], process, descriptors)
    attempted, captures = filtered_index_rows(events)
    if index.get('attempted_entries') != attempted:
        raise ValueError('The raw classification rows differ from the exact guard counters.')
    if index.get('captured_entries') != captures:
        raise ValueError('The raw capture rows differ from the exact native entries.')
    coverage = trace['coverage']
    for key in ('attempted_entries', 'actual_triggers', 'unknown_guards', 'entry_events', 'captured_events'):
        if coverage.get(key) != events.coverage[key]:
            raise ValueError('Filtered coverage differs from the raw event identities: ' + key)
    retained = [(point.get('trigger', {}).get('rule'), point.get('trigger', {}).get('client'),
                 point.get('trigger', {}).get('invocation')) for point in trace['points']]
    expected = [(row['rule'], row['client'], row['invocation']) for row in captures]
    if retained != expected:
        raise ValueError('The retained points differ from the exact filtered captures.')
    if trace.get('completion', {}).get('trace_complete') is True and not events.coverage['required_complete']:
        raise ValueError('Incomplete filtered event coverage cannot establish completeness.')
    lookups = [row['reference'] for row in events.checkpoints if row['label'] == 'instruction-lookup']
    checkpoints = [row['reference'] for row in events.checkpoints if row['label'] == 'requested-trigger']
    if index.get('instruction_lookups') != lookups or index.get('requested_checkpoints') != checkpoints:
        raise ValueError('The raw checkpoint index differs from its exact native records.')
    return {'selection_policy': 'source-filtered-v1', 'attempted_entries': attempted,
            'captured_entries': captures, 'coverage': events.coverage}
