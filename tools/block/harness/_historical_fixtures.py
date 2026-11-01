"""Materialize derived test data. This data never supplies admission evidence."""
import atexit
import gzip
import hashlib
import json
import os
from pathlib import Path
import tempfile

HERE = Path(__file__).resolve().parent
BUNDLE = HERE / 'test-fixtures/historical-inputs'
_ROOT = None
_DONE = {}
_HASHES = {}
_BUILDING = set()
_MANIFEST = None


def _manifest():
    global _MANIFEST
    if _MANIFEST is None:
        _MANIFEST = json.loads((BUNDLE / 'MANIFEST.json').read_text())
        if _MANIFEST['schema'] != 'harness.authentic-fixtures.v1':
            raise ValueError('The authentic fixture manifest has another schema.')
    return _MANIFEST


def root():
    global _ROOT
    if _ROOT is None:
        # The fixture filesystem supports the production reflink controls.
        parent = Path(os.environ.get('TMPDIR', '/home/cody/.cache/zesislar-registry-tests-worker2'))
        parent.mkdir(parents=True, exist_ok=True)
        _ROOT = Path(tempfile.mkdtemp(prefix='derived-harness-fixtures-', dir=parent))
        owner = os.getpid()
        def cleanup():
            if os.getpid() == owner:
                import shutil
                shutil.rmtree(_ROOT)
        atexit.register(cleanup)
    return _ROOT


def relocated(value):
    for prefix, relative in _manifest()['roots'].items():
        if value == prefix or value.startswith(prefix + '/'):
            return str(root() / relative) + value[len(prefix):]
    return value


def _transform(value):
    if isinstance(value, dict):
        return {_transform(key): _transform(item) for key, item in value.items()}
    if isinstance(value, list):
        return [_transform(item) for item in value]
    if isinstance(value, str):
        choices = _manifest()['hashes'].get(value, [])
        if choices:
            materialize(choices[0])
            return _HASHES[choices[0]]
        return relocated(value)
    return value


def materialize(origin):
    """Preserve source bytes. Relocate typed JSON paths and dependent hashes."""
    origin = str(origin)
    if origin in _DONE:
        return _DONE[origin]
    if origin in _BUILDING:
        raise ValueError('The fixture hash dependencies contain a cycle: ' + origin)
    row = _manifest()['files'].get(origin)
    if row is None:
        raise FileNotFoundError('An authentic fixture is unavailable: ' + origin)
    payload = gzip.decompress((BUNDLE / 'authentic' / (row['sha256'] + '.gz')).read_bytes())
    if hashlib.sha256(payload).hexdigest() != row['sha256'] or len(payload) != row['size']:
        raise ValueError('The authentic fixture bytes changed: ' + origin)
    target = Path(relocated(origin))
    if not target.is_relative_to(root()):
        raise ValueError('A derived fixture leaves its owned directory.')
    _BUILDING.add(origin)
    try:
        if row['format'] == 'json':
            value=json.loads(payload)
            if row.get('replacement_legacy_claims'):
                # Retain all real ledger rows. Relocate only consumed release records.
                for claim in row['replacement_legacy_claims']:
                    value['fixed_claim_releases'][claim]=_transform(value['fixed_claim_releases'][claim])
            else:
                value=_transform(value)
            payload = (json.dumps(value, indent=2, ensure_ascii=False) + '\n').encode()
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes(payload)
        target.chmod(row['mode'])
        _DONE[origin] = target
        _HASHES[origin] = hashlib.sha256(payload).hexdigest()
    finally:
        _BUILDING.remove(origin)
    return target


def prepare():
    """Materialize available inputs. Keep missing historical evidence absent."""
    for origin in _manifest()['files']:
        materialize(origin)
    return root()


def read_json(path):
    """Derive an existing tracked container without changing its authentic file."""
    return _transform(json.loads(Path(path).read_bytes()))


def directory(origin):
    prepare()
    return Path(relocated(str(origin)))


def use_policy(test):
    """Bind derived policy data only within one unit test's context."""
    from unittest.mock import patch
    import memory_policy
    release = '/home/cody/zesislar/_build/agents/worker-build-2/PORT-matrix006-authority-v1/'
    for field, name in [('PORT_AUTHORITY','PORT-FAMILY-AUTHORITY-22-v31.json'),
                        ('PORT_EXTENSION','EXTENSION.json')]:
        target = materialize(release + name)
        value = {'path':str(target),'sha256':hashlib.sha256(target.read_bytes()).hexdigest()}
        test.enterContext(patch.object(memory_policy,field,value))
