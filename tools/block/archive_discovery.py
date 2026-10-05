#!/usr/bin/env python3
"""Preserve complete capture bytes and emit bounded discovery evidence."""
import hashlib
import json
from pathlib import Path


def store(archive, data):
    digest = hashlib.sha256(data).hexdigest()
    path = Path(archive) / digest[:2] / digest
    path.parent.mkdir(parents=True, exist_ok=True)
    if path.exists() and path.read_bytes() != data:
        raise ValueError('The archive has a conflicting hash record')
    if not path.exists():
        path.write_bytes(data)
    if hashlib.sha256(path.read_bytes()).hexdigest() != digest:
        raise ValueError('The archive failed byte verification')
    return {'sha256': digest, 'archive_path': str(path.resolve()), 'bytes': len(data)}


def bounded_report(report, artifacts, archive):
    """Keep exact conclusions; bind complete goals and captures by hash."""
    result = {key: value for key, value in report.items() if key != 'blocks'}
    result['artifacts'] = artifacts
    result['blocks'] = []
    for block in report['blocks']:
        row = {key: value for key, value in block.items() if key != 'captures'}
        residual = block.get('first_residual')
        if isinstance(residual, dict) and 'conclusion' in residual:
            row['first_residual'] = {'conclusion': residual['conclusion'],
                                     'full_goal': store(archive, (json.dumps(residual, sort_keys=True) + '\n').encode())}
        row['captures'] = []
        for capture in block['captures']:
            fields = ('entry', 'exit', 'outcome', 'performance', 'error', 'residual_pcs',
                      'residual_location', 'proof_phase_entered', 'source_sha256',
                      'pet_peak_mib', 'rss_uses_unique_processes', 'inherited_debts',
                      'search_failure', 'last_valid_goals', 'failed_command')
            bounded = {key: capture[key] for key in fields if key in capture}
            bounded['pending_goal_count'] = len(capture.get('pending_goals', []))
            bounded['shelved_goal_count'] = len(capture.get('shelved_goals', []))
            bounded['full_capture'] = store(archive, (json.dumps(capture, sort_keys=True) + '\n').encode())
            row['captures'].append(bounded)
        result['blocks'].append(row)
    return result


def diagnose_capture(capture, calls):
    """Distinguish query timeouts from tactic timeouts without inferring progress."""
    result = dict(capture)
    result['raw_outcome'] = capture['outcome']
    failures = [call for call in calls if call.get('success') is False]
    failure = failures[-1] if failures else {}
    if not capture.get('proof_phase_entered') and failure.get('reason') == 'timeout':
        result['outcome'] = 'setup-timeout'
        result['search_failure'] = {'stage': 'rocq_start', 'reason': 'server-query-timeout',
                                    'pet_restarted': failure.get('pet_restarted'),
                                    'proof_execution': False, 'pet_peak_available': False}
    elif (capture.get('proof_phase_entered') and failure.get('error') == 'Coq: Timeout!'
          and failure.get('reason') == 'tactic_failed'):
        result['outcome'] = 'automation-search-timeout'
        result['failed_command'] = failure.get('failed_command')
        result['last_valid_goals'] = failure.get('goals_at_failure')
        result['search_failure'] = {'stage': 'rocq_check', 'reason': 'Coq-tactic-timeout',
                                    'progressed_residual_available': False,
                                    'goal_scope': 'The failed transaction returned its last valid state'}
    elif capture['outcome'] == 'reached':
        result['outcome'] = 'abstract-successor-reached'
    return result
