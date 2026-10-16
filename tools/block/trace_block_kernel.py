"""Verify bounded-display markers against pinned Marshal reload evidence.

Python checks byte identities and receipt associations. The pinned OCaml reader
performs Marshal reload. Neither check establishes kernel typechecking.
"""
import hashlib
import json
from pathlib import Path, PurePosixPath
import re

MAX_RECORD_BYTES = 2_097_152
REASONS = {'depth-limit', 'shared-reference', 'node-budget'}
CHECKS = {'hash', 'bytes', 'schema', 'toolchain', 'context', 'evar_references',
          'remarshal_bytes', 'trailing_bytes_absent'}


def _fields(value, names):
    if not isinstance(value, dict) or set(value) != set(names.split()):
        raise ValueError('The kernel evidence has unsupported fields.')


def _hash(value):
    if not isinstance(value, str) or re.fullmatch('[0-9a-f]{64}', value) is None:
        raise ValueError('The kernel artifact hash is invalid.')
    return value


def _integer(value, minimum=0):
    if type(value) is not int or value < minimum:
        raise ValueError('The kernel evidence integer is invalid.')
    return value


def _digest(path):
    digest = hashlib.sha256()
    with path.open('rb') as stream:
        for chunk in iter(lambda: stream.read(1_048_576), b''):
            digest.update(chunk)
    return digest.hexdigest()


def artifact(root, reference):
    """Check a regular artifact without following an evidence symlink."""
    _fields(reference, 'path sha256 bytes')
    _integer(reference['bytes'])
    _hash(reference['sha256'])
    name = reference['path']
    if (not isinstance(name, str) or not name or PurePosixPath(name).is_absolute()
            or any(part in ('', '.', '..') for part in name.split('/'))):
        raise ValueError('The kernel artifact path leaves its evidence root.')
    path = Path(root).resolve(strict=True)
    for part in name.split('/'):
        path = path / part
        if path.is_symlink():
            raise ValueError('The kernel artifact path contains a symlink.')
    if not path.is_file() or path.stat().st_size != reference['bytes'] or _digest(path) != reference['sha256']:
        raise ValueError('The kernel artifact bytes differ from their exact reference.')
    return path


def _json(path):
    if path.stat().st_size > MAX_RECORD_BYTES:
        raise ValueError('The kernel JSON record exceeds the serialized byte limit.')
    def unique(pairs):
        value = {}
        for key, item in pairs:
            if key in value:
                raise ValueError('The kernel JSON record repeats a field.')
            value[key] = item
        return value
    def invalid(value):
        raise ValueError('The kernel JSON record has a nonfinite number.')
    return json.loads(path.read_text(encoding='utf-8'), object_pairs_hook=unique, parse_constant=invalid)


def _reader(reference):
    """Check the executable identity supplied by the sealed runtime."""
    _fields(reference, 'path sha256')
    _hash(reference['sha256'])
    if not isinstance(reference['path'], str):
        raise ValueError('The pinned Marshal reader path is invalid.')
    path = Path(reference['path'])
    if not path.is_absolute() or not path.is_file() or _digest(path) != reference['sha256']:
        raise ValueError('The pinned Marshal reader identity differs.')


def display_token(marker):
    return '<kernel-elision sha256=%s bytes=%d reason=%s>' % (
        marker['sha256'], marker['bytes'], marker['reason'])


def verify_kernel_marker(root, marker, reload_receipt, *, expected_toolchain_ref, expected_reader):
    """Require every artifact and an exact accepted pinned-reader receipt.

    The caller supplies toolchain and reader identities from its sealed runtime.
    This function does not infer those identities from the supplied receipt.
    """
    _fields(marker, 'schema kind reason depth sha256 bytes hash_scope size_unit sidecar context_ref evar_catalog_ref toolchain_ref')
    if type(marker['schema']) is not int or marker['schema'] != 1 or marker['kind'] != 'kernel-elision':
        raise ValueError('The kernel marker schema or kind is unsupported.')
    if not isinstance(marker['reason'], str) or marker['reason'] not in REASONS or marker['hash_scope'] != 'pinned-marshal-bytes' or marker['size_unit'] != 'bytes':
        raise ValueError('The kernel marker has an unsupported elision or size meaning.')
    serialized = 0
    for part in json.JSONEncoder(ensure_ascii=False, allow_nan=False).iterencode(marker):
        serialized += len(part.encode('utf-8'))
        if serialized > MAX_RECORD_BYTES:
            raise ValueError('The kernel marker exceeds the serialized byte limit.')
    _integer(marker['depth'])
    _integer(marker['bytes'])
    _hash(marker['sha256'])
    if marker['toolchain_ref'] != expected_toolchain_ref:
        raise ValueError('The kernel marker has an incompatible toolchain identity.')
    _reader(expected_reader)
    for field in ('sidecar', 'context_ref', 'evar_catalog_ref', 'toolchain_ref'):
        artifact(root, marker[field])
    if (marker['sha256'] != marker['sidecar']['sha256']
            or marker['bytes'] != marker['sidecar']['bytes']):
        raise ValueError('The kernel marker and sidecar identities differ.')
    receipt = _json(artifact(root, reload_receipt))
    _fields(receipt, 'schema kind sidecar context_ref evar_catalog_ref toolchain_ref reader accepted checks kernel_typecheck error')
    if (type(receipt['schema']) is not int or receipt['schema'] != 1
            or receipt['kind'] != 'kernel-marshal-reload'):
        raise ValueError('The Marshal reload receipt has an unsupported schema.')
    for field in ('sidecar', 'context_ref', 'evar_catalog_ref', 'toolchain_ref'):
        if receipt[field] != marker[field]:
            raise ValueError('The Marshal reload receipt has a different ' + field + ' identity.')
    if receipt['reader'] != expected_reader:
        raise ValueError('The Marshal reload receipt names another reader.')
    if (receipt['accepted'] is not True or receipt['kernel_typecheck'] != 'not-attempted'
            or receipt['error'] is not None or not isinstance(receipt['checks'], dict)
            or set(receipt['checks']) != CHECKS or any(value is not True for value in receipt['checks'].values())):
        raise ValueError('The Marshal reload receipt does not establish complete serialization preservation.')
    return {'display_availability': 'bounded', 'display_token': display_token(marker),
            'kernel_artifact': 'reload-verified', 'hash_scope': 'pinned-marshal-bytes',
            'size_unit': 'bytes', 'bytes': marker['bytes'], 'sha256': marker['sha256'],
            'reload_receipt': reload_receipt, 'kernel_typecheck': 'not-attempted',
            'limit': 'The receipt establishes graph-byte preservation. It does not establish kernel typechecking or semantic equality.'}
