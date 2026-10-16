"""Keep selected feedback omissions separate from captured messages."""
from collections.abc import Mapping

POLICY = 'trigger-selected-raw-v2'


def selected_feedback(status):
    """Check the schema410 counters from an independently checked status query."""
    if status is None:
        return {'availability': 'unavailable',
                'reason': 'The checked status has no selected-feedback record.'}
    if not isinstance(status, Mapping):
        raise ValueError('The selected-feedback status is unsupported.')
    value = status.get('selected_feedback')
    if value is None:
        return {'availability': 'unavailable',
                'reason': 'The checked status has no selected-feedback record.'}
    if (not isinstance(value, Mapping)
            or set(value) != {'emitted', 'omitted', 'complete', 'first_error'}):
        raise ValueError('The selected-feedback record has unsupported fields.')
    for name in ('emitted', 'omitted'):
        if type(value[name]) is not int or value[name] < 0:
            raise ValueError('The selected-feedback count is invalid.')
    if type(value['complete']) is not bool or value['complete'] != (value['omitted'] == 0):
        raise ValueError('The selected-feedback completeness contradicts its count.')
    if value['omitted'] == 0:
        if value['first_error'] is not None:
            raise ValueError('The selected-feedback error contradicts its count.')
    elif not isinstance(value['first_error'], str) or not value['first_error']:
        raise ValueError('The omitted selected feedback lacks its exact first error.')
    return {'availability': 'complete' if value['complete'] else 'partial',
            'scope': 'Selected entry hand trials and selected original callback.',
            'status': dict(value)}


def apply_selected_feedback(points, status):
    """Apply schema410 only for a caller that selected the new raw policy."""
    checked = selected_feedback(status)
    for point in points:
        point['hint_log']['availability'] = checked['availability']
        point['hint_log']['selected_feedback'] = dict(checked)
        point['hint_log']['selected_feedback']['evidence'] = (
            'evidence/SESSION.json#/observer_status/status/selected_feedback')
    return checked


def raw_policy(request):
    """Reject malformed runtime declarations instead of selecting legacy behavior."""
    runtime = request.get('observer_runtime', {})
    if not isinstance(runtime, Mapping):
        raise ValueError('The observer runtime declaration is unsupported.')
    if 'raw_policy' not in runtime:
        return None
    if runtime['raw_policy'] != POLICY:
        raise ValueError('The declared raw policy is unsupported.')
    return POLICY


def checked_status_payload(root, response):
    """Read the exact query payload once with bounded reads and hash validation."""
    import hashlib
    import json
    from pathlib import Path
    root = Path(root).resolve(strict=True)
    path = Path(response['path'])
    if not path.is_absolute() or not path.is_relative_to(root):
        raise ValueError('The status payload leaves its owned evidence root.')
    relative = path.relative_to(root)
    if any(part in ('.', '..') for part in relative.parts):
        raise ValueError('The status payload path is unsupported.')
    current = root
    for part in relative.parts:
        current = current / part
        if current.is_symlink():
            raise ValueError('The status payload path contains a symlink.')
    with path.open('rb') as stream:
        payload = stream.read(2 * 1024 * 1024 + 1)
    if len(payload) > 2 * 1024 * 1024:
        raise ValueError('The status payload exceeds the physical record limit.')
    if hashlib.sha256(payload).hexdigest() != response['sha256']:
        raise ValueError('The parsed status payload differs from its checked reference.')
    def unique(pairs):
        value = {}
        for key, item in pairs:
            if key in value:
                raise ValueError('The status payload repeats a JSON field.')
            value[key] = item
        return value
    return json.loads(payload.decode('utf-8'), object_pairs_hook=unique)


def bind_selected_feedback(events, status):
    """Check every owned feedback payload before any SDK-discarded partition."""
    checked = selected_feedback(status)
    sequences = []
    for reference in events.references:
        row = events.read(reference)
        if row['kind'] != 'feedback':
            continue
        text = events.text_field(reference, 'message')
        if isinstance(text, str):
            pass
        else:
            for fragment in text.iter_text():
                if not isinstance(fragment, str):
                    raise ValueError('A selected-feedback fragment is unsupported.')
        sequences.append(row['sequence'])
    if len(sequences) != len(set(sequences)):
        raise ValueError('The selected-feedback event sequence repeats.')
    if 'status' in checked and checked['status']['emitted'] != len(sequences):
        raise ValueError('The selected-feedback emitted count differs from the owned events.')
    checked['verified_event_count'] = len(sequences)
    return checked
