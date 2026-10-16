"""Check a final raw-budget ledger against externally sealed file bytes."""
from collections.abc import Mapping
import hashlib
import json
from pathlib import Path, PurePosixPath

RAW_LIMIT_BYTES = 2_000_000_000
LEDGER_BYTES = 8192
CONTROL_RESERVE_BYTES = 1_048_576
LEDGER_PATH = 'evidence/RAW-BUDGET.json'
POLICY = 'trigger-selected-raw-v2'


def _integer(value, minimum=0):
    if type(value) is not int or value < minimum:
        raise ValueError('The raw budget has an invalid integer.')


def _fields(value, names):
    if not isinstance(value, Mapping) or set(value) != set(names.split()):
        raise ValueError('The raw budget has unsupported fields.')


def _relative(name):
    if (not isinstance(name, str) or not name or PurePosixPath(name).is_absolute()
            or any(part in ('', '.', '..') for part in name.split('/')) or '\x00' in name):
        raise ValueError('The raw budget has an unsafe relative path.')


def _unique(pairs):
    value = {}
    for key, item in pairs:
        if key in value:
            raise ValueError('The raw budget contains a duplicate JSON field.')
        value[key] = item
    return value


def validate_ledger(ledger, raw_root, actual_bytes, *, expected_limit=RAW_LIMIT_BYTES):
    """Check ledger content. The caller independently seals its exact bytes."""
    _fields(ledger, 'schema root limit_bytes control_reserve_bytes used_bytes complete denied_writes first_denial')
    if type(ledger['schema']) is not int or ledger['schema'] != 1:
        raise ValueError('The raw budget schema is unsupported.')
    _integer(expected_limit, LEDGER_BYTES + CONTROL_RESERVE_BYTES)
    if expected_limit > RAW_LIMIT_BYTES:
        raise ValueError('The expected raw budget exceeds the native ceiling.')
    if ledger['root'] != str(Path(raw_root).resolve(strict=True)):
        raise ValueError('The raw budget belongs to another raw root.')
    for name in ('limit_bytes', 'control_reserve_bytes', 'used_bytes', 'denied_writes'):
        _integer(ledger[name])
    if ledger['limit_bytes'] != expected_limit or ledger['control_reserve_bytes'] != CONTROL_RESERVE_BYTES:
        raise ValueError('The raw budget differs from its fixed limits.')
    _integer(actual_bytes, LEDGER_BYTES)
    if not actual_bytes <= ledger['used_bytes'] <= expected_limit:
        raise ValueError('The raw bytes exceed their reservation or ceiling.')
    if type(ledger['complete']) is not bool or ledger['complete'] != (ledger['denied_writes'] == 0):
        raise ValueError('The raw budget completeness contradicts its denials.')
    if ledger['denied_writes'] == 0:
        if ledger['first_denial'] is not None:
            raise ValueError('The complete raw budget has a denial record.')
    else:
        denial = ledger['first_denial']
        _fields(denial, 'path requested_bytes channel')
        _relative(denial['path'])
        _integer(denial['requested_bytes'])
        if denial['channel'] not in ('data', 'control'):
            raise ValueError('The raw denial has an unsupported channel.')
    return ledger


def verify_raw_budget(raw_root, session, raw_seal_reference, *, expected_limit=RAW_LIMIT_BYTES):
    """Validate final evidence. Smaller explicit limits identify synthetic controls."""
    from trace_block_seal import checked_reference, file_sha256, verify_root_seal
    root = Path(raw_root).resolve(strict=True)
    if (not isinstance(raw_seal_reference, Mapping)
            or set(raw_seal_reference) not in ({'path', 'sha256'}, {'path', 'sha256', 'bytes'})):
        raise ValueError('The raw budget lacks its exact external seal reference.')
    seal_path = checked_reference(dict(raw_seal_reference))
    if seal_path.resolve().is_relative_to(root):
        raise ValueError('The raw-budget seal is inside its raw root.')
    seal_payload = seal_path.read_bytes()
    if (hashlib.sha256(seal_payload).hexdigest() != raw_seal_reference['sha256']
            or ('bytes' in raw_seal_reference and len(seal_payload) != raw_seal_reference['bytes'])):
        raise ValueError('The parsed raw seal differs from its exact reference.')
    record = json.loads(seal_payload.decode('utf-8'), object_pairs_hook=_unique)
    _fields(record, 'schema_version root session_id files')
    if type(record['schema_version']) is not int or record['schema_version'] != 1:
        raise ValueError('The raw-budget seal schema is unsupported.')
    for path in root.rglob('*'):
        if path.is_symlink() or not (path.is_file() or path.is_dir()):
            raise ValueError('The raw budget contains an unsupported raw link or file type.')
    verification = verify_root_seal(root / 'evidence', record['session_id'], seal_path)
    if file_sha256(seal_path) != raw_seal_reference['sha256']:
        raise ValueError('The raw-budget seal changed during verification.')
    if record['root'] != str(root):
        raise ValueError('The raw-budget seal belongs to another raw root.')
    rows = record['files']
    actual_bytes = sum(row['bytes'] for row in rows)
    ledgers = [row for row in rows if row['path'] == LEDGER_PATH]
    if len(ledgers) != 1 or ledgers[0]['bytes'] != LEDGER_BYTES:
        raise ValueError('The raw seal lacks the exact fixed-size ledger.')
    ledger_path = root / LEDGER_PATH
    if ledger_path.is_symlink():
        raise ValueError('The raw-budget ledger is a symlink.')
    payload = ledger_path.read_bytes()
    if len(payload) != LEDGER_BYTES or not payload.endswith(b'\n'):
        raise ValueError('The raw-budget ledger has a different physical size or padding.')
    if hashlib.sha256(payload).hexdigest() != ledgers[0]['sha256']:
        raise ValueError('The parsed ledger bytes differ from the external raw seal.')
    ledger = json.loads(payload.decode('utf-8'), object_pairs_hook=_unique)
    validate_ledger(ledger, root, actual_bytes, expected_limit=expected_limit)
    session_reference = None
    reasons = []
    if not ledger['complete']:
        reasons.append('The raw writer refused a write at its ceiling.')
    if session is None:
        reasons.append('The final SESSION is unavailable.')
    else:
        from trace_block_kernel_display import _exact
        if not isinstance(session, Mapping):
            raise ValueError('The raw-budget SESSION is unsupported.')
        sessions = [row for row in rows if row['path'] == 'evidence/SESSION.json']
        if len(sessions) != 1:
            raise ValueError('The supplied SESSION lacks its exact sealed raw file.')
        session_path = root / 'evidence/SESSION.json'
        if session_path.is_symlink():
            raise ValueError('The raw-budget SESSION is a symlink.')
        session_payload = session_path.read_bytes()
        if (len(session_payload) != sessions[0]['bytes']
                or hashlib.sha256(session_payload).hexdigest() != sessions[0]['sha256']):
            raise ValueError('The parsed SESSION bytes differ from the external raw seal.')
        retained_session = json.loads(session_payload.decode('utf-8'), object_pairs_hook=_unique)
        if not _exact(retained_session, session):
            raise ValueError('The supplied SESSION differs from its sealed parsed content.')
        session_reference = dict(sessions[0])
        value = session.get('raw_budget')
        _fields(value, 'ledger_path limit_bytes complete')
        if (value['ledger_path'] != LEDGER_PATH or type(value['limit_bytes']) is not int
                or value['limit_bytes'] != expected_limit or type(value['complete']) is not bool
                or value['complete'] != ledger['complete']):
            raise ValueError('The SESSION differs from its final raw ledger.')
        status = session.get('observer_status')
        if status is None:
            reasons.append('The final observer status is unavailable.')
        else:
            observer = status.get('status') if isinstance(status, Mapping) else None
            if not isinstance(observer, Mapping):
                raise ValueError('The raw-budget observer status is unsupported.')
            value = observer.get('raw_budget')
            _fields(value, 'schema limit_bytes limit_reached ledger')
            if (type(value['schema']) is not int or value['schema'] != 1
                    or type(value['limit_bytes']) is not int or value['limit_bytes'] != expected_limit
                    or type(value['limit_reached']) is not bool
                    or value['limit_reached'] != (not ledger['complete'])
                    or value['ledger'] != LEDGER_PATH):
                raise ValueError('The observer differs from its final raw ledger.')
            if observer.get('complete') is not True:
                reasons.append('The final observer is incomplete.')
            elif not ledger['complete']:
                raise ValueError('An exhausted raw ledger cannot establish complete observation.')
    return {'schema': 1, 'policy': POLICY,
            'scope': 'native-limit' if expected_limit == RAW_LIMIT_BYTES else 'synthetic-smaller-limit',
            'ledger': {'path': LEDGER_PATH, 'sha256': hashlib.sha256(payload).hexdigest(), 'bytes': LEDGER_BYTES},
            'raw_seal': {'path': str(seal_path), 'sha256': file_sha256(seal_path)},
            'session': session_reference,
            'raw_verification': verification, 'actual_bytes': actual_bytes,
            'reserved_bytes': ledger['used_bytes'], 'limit_bytes': expected_limit,
            'limit_reached': not ledger['complete'], 'complete': not reasons, 'reasons': reasons,
            'coverage_limit': 'This ledger check does not establish event coverage, operation joins, or proof closure.'}
