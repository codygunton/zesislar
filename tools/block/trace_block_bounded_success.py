"""Check named-rule success from independently verified bounded captures.

This pure helper does not validate Marshal bytes or reload receipts. The caller
must first validate BoundedCapture artifacts and exact operation associations.
Unresolved artifact aliases cannot satisfy this raw-projection interface.
"""
from collections.abc import Mapping, Sequence
import re


class _Unavailable(ValueError):
    pass


def _require(condition):
    if not condition:
        raise _Unavailable()


def _array(value):
    return isinstance(value, Sequence) and not isinstance(value, (str, bytes, bytearray))


def _reference(value):
    _require(isinstance(value, Mapping) and set(value) == {'path', 'sha256', 'bytes'})
    _require(isinstance(value['path'], str) and value['path']
             and not value['path'].startswith('/')
             and all(part not in ('', '.', '..') for part in value['path'].split('/')))
    _require(isinstance(value['sha256'], str) and re.fullmatch('[0-9a-f]{64}', value['sha256']))
    _require(type(value['bytes']) is int and value['bytes'] >= 0)
    return {key: value[key] for key in ('path', 'sha256', 'bytes')}


def _key(reference):
    _require(isinstance(reference, str) and reference.startswith('#/snapshots/'))
    value = reference[len('#/snapshots/'):]
    _require(value and '/' not in value and not re.search('~(?![01])', value))
    return value.replace('~1', '/').replace('~0', '~')


def _pointer(key):
    _require(isinstance(key, str) and key)
    return '#/snapshots/' + key.replace('~', '~0').replace('/', '~1')


def _snapshot(snapshots, pointer):
    value = snapshots[_key(pointer)]
    _require(isinstance(value, Mapping) and value.get('surface_policy') == 'bounded-kernel-v1')
    _require(value.get('evars', {}).get('availability') == 'complete-referenced')
    _require(value.get('completeness', {}).get('printed_terms') == 'bounded'
             and value['completeness'].get('complete_terms') == 'marshal-reload-and-membership-verified')
    _reference(value['complete_sidecar'])
    _require(type(value.get('fresh_evar_counter')) is int and value['fresh_evar_counter'] >= 0)
    for group in ('current_goals', 'shelf', 'given_up'):
        _require(_array(value[group]))
        ids = [row['id'] for row in value[group]]
        _require(all(type(key) is int and key >= 0 for key in ids) and len(set(ids)) == len(ids))
    return value


def _state(value):
    sidecar = _reference(value['complete_sidecar'])
    return (sidecar['sha256'], sidecar['bytes'], value['fresh_evar_counter'],
            tuple(tuple(row['id'] for row in value[group])
                  for group in ('current_goals', 'shelf', 'given_up')))


def _entries(snapshot):
    entries = snapshot['evars']['entries']
    _require(_array(entries))
    result = {}
    for entry in entries:
        key = entry['id']
        _require(type(key) is int and key >= 0 and key not in result)
        _require(entry['status'] in ('defined', 'undefined'))
        if entry['status'] == 'defined':
            body = entry['body']
            _require(isinstance(body, Mapping)
                     and set(body) == {'availability', 'complete_sidecar', 'node_ref'})
            _require(body['availability'] == 'referenced'
                     and body['complete_sidecar'] == snapshot['complete_sidecar']
                     and body['node_ref'] == {'root_id': 'evar/%d/body' % key, 'child_path': []})
        else:
            _require(entry['body'] is None)
        result[key] = entry
    return result


def rule_success(point, snapshots, expected_command, session_id, *, expected_rule,
                 trial_index=None):
    """Return one exact terminal trial certificate, or None when unavailable.

    The default selects the first valid occurrence in recorded order. A diagnosis
    can request one exact occurrence with trial_index. Earlier obligations may
    remain. The targeted entry evars must become defined, without new undefined
    evars. Defined raw group members are not obligations. No global branch-survival
    claim follows.
    """
    try:
        _require(isinstance(point, Mapping) and isinstance(snapshots, Mapping))
        _require(isinstance(session_id, str) and session_id
                 and point.get('session_id') == session_id)
        _require(isinstance(expected_rule, str) and expected_rule
                 and isinstance(expected_command, str) and expected_command.strip())
        trigger = point['trigger']
        _require(trigger['kind'] == 'rule-entry' and trigger['rule'] == expected_rule)
        _require(isinstance(trigger['client'], str) and trigger['client'])
        invocation = trigger['invocation']
        _require(type(invocation) is int and invocation > 0)
        operation = point['operation']
        _require(operation['availability'] == 'complete' and operation['trial'] is False)
        _require(isinstance(operation['session_operation'], str)
                 and operation['session_operation'].startswith('evidence/SESSION.json#/operations/'))
        _require(_array(point['hand_call']))
        if trial_index is None:
            indexes = range(len(point['hand_call']))
        else:
            _require(type(trial_index) is int and 0 <= trial_index < len(point['hand_call']))
            indexes = [trial_index]
        for index in indexes:
            try:
                trial = point['hand_call'][index]
                _require(trial['clause'] == 'whole-rule' and trial['outcome'] == 'accepted'
                         and trial['command'] == expected_command and trial['rollback_equal'] is True)
                trial_id = 'invocation-%d-occurrence-%d' % (invocation, index + 1)
                _require(trial['trial_id'] == trial_id)
                trial_operation = trial['operation']
                _require(trial_operation['availability'] == 'complete'
                         and trial_operation['trial'] is False
                         and trial_operation['session_operation'] == operation['session_operation'])
                _require(_array(trial['commands']) and trial['commands'])
                commands = trial['commands']
                _require(all(command['outcome'] == 'accepted' and command['refusal'] is None
                             for command in commands))
                _require(commands[-1]['command'] == expected_command)
                before_ref, after_ref = commands[0]['before'], commands[-1]['after']
                rollback_ref = _pointer(trial['rollback'])
                _require(_key(before_ref) == trial['before'] and _key(after_ref) == trial['after_trial'])
                _require(not str(trial.get('after_trial_availability', '')).startswith('unavailable'))
                before = _snapshot(snapshots, before_ref)
                after = _snapshot(snapshots, after_ref)
                rollback = _snapshot(snapshots, rollback_ref)
                _require(_state(before) == _state(rollback) == _state(point))
                _require(all(_key(a['after']) == _key(b['before'])
                             for a, b in zip(commands, commands[1:])))
                before_entries, after_entries = _entries(before), _entries(after)
                targeted = [row['id'] for row in before['current_goals']]
                _require(targeted and all(before_entries[key]['status'] == 'undefined'
                                         and after_entries[key]['status'] == 'defined' for key in targeted))
                before_undefined = [key for key, row in before_entries.items() if row['status'] == 'undefined']
                after_undefined = [key for key, row in after_entries.items() if row['status'] == 'undefined']
                _require(set(after_undefined) <= set(before_undefined))
                return {'schema': 1, 'kind': 'rule_success', 'scope': 'named-rule',
                    'session': session_id, 'rule': expected_rule, 'client': trigger['client'],
                    'command': expected_command, 'trial_id': trial_id, 'trial_index': index,
                    'before': before_ref, 'after': after_ref, 'rollback': rollback_ref,
                    'entry_goal_evars': targeted, 'before_undefined_evars': before_undefined,
                    'after_undefined_evars': after_undefined,
                    'before_complete_sidecar': _reference(before['complete_sidecar']),
                    'after_complete_sidecar': _reference(after['complete_sidecar']),
                    'rollback_complete_sidecar': _reference(rollback['complete_sidecar']),
                    'operation': dict(operation), 'native_branch_survival': 'unavailable'}
            except (_Unavailable, KeyError, TypeError, IndexError):
                continue
        return None
    except (_Unavailable, KeyError, TypeError, IndexError):
        return None
