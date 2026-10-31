"""Immutable native block results, keyed by the complete search inputs.

The caller supplies the checked import closure and selected entry declarations.
An entry module must use its full source digest unless the caller checks the
selected declarations and all remaining context. Cache hits are observations,
not new proof executions or permission to reuse objects in another library.
"""
import clone_copy
import argparse
from copy import deepcopy
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import tempfile
import time
import uuid


SCHEMA = 'entry-chain.result-cache.v1'
KEY_SCHEMA = 'entry-chain.result-key.v1'


class CacheDefect(ValueError):
    def __init__(self, record):
        self.record = record
        super().__init__('The cache entry failed validation and was evicted.')


def enabled(purpose='exploration'):
    if purpose not in {'exploration', 'confirmation', 'gate', 'merge'}:
        raise ValueError('The cache purpose is unsupported.')
    setting = os.environ.get('ZESU_PROOF_CACHE', 'on')
    if setting not in {'on', 'off'}:
        raise ValueError('ZESU_PROOF_CACHE must be on or off.')
    return purpose == 'exploration' and setting == 'on' and os.environ.get('ZESU_IO') != 'gate'


def digest(path):
    h = hashlib.sha256()
    with Path(path).open('rb') as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b''):
            h.update(chunk)
    return h.hexdigest()


def encoded(value):
    return (json.dumps(value, sort_keys=True, separators=(',', ':'),
                       allow_nan=False) + '\n').encode()


def semantic_digest(identity):
    if identity.get('key_function') == 'zesu-proof-attempt-v1':
        from proof_cache_key import ATTEMPT_SCHEMA, identity as key_identity
        return key_identity(ATTEMPT_SCHEMA, identity)
    return hashlib.sha256(encoded(identity)).hexdigest()


def checked_digest(value):
    if not isinstance(value, str) or not re.fullmatch('[0-9a-f]{64}', value):
        raise ValueError('A cache input has an invalid SHA256 digest.')
    return value


def source_identity(row):
    """Check a source binding, then remove only its physical location."""
    if not isinstance(row, dict) or set(row) - {'path', 'sha256', 'bytes'}:
        raise ValueError('A source binding has unsupported fields.')
    expected = checked_digest(row['sha256'])
    if 'path' in row:
        path = Path(row['path'])
        if digest(path) != expected:
            raise ValueError('A cache input changed.')
        if 'bytes' in row and path.stat().st_size != row['bytes']:
            raise ValueError('A cache input size changed.')
    return {'sha256': expected}


def named_sources(rows, label):
    if not isinstance(rows, list) or not rows:
        raise ValueError(f'The {label} identity list is empty.')
    answer = []
    for row in rows:
        if set(row) != {'name', 'source'} or not isinstance(row['name'], str) or not row['name']:
            raise ValueError(f'The {label} identity has unsupported fields.')
        answer.append({'name': row['name'], 'source': source_identity(row['source'])})
    if len({row['name'] for row in answer}) != len(answer):
        raise ValueError(f'The {label} identity contains duplicate names.')
    return sorted(answer, key=lambda row: row['name'])


def bound_identity(spec):
    """Provisional raw-source identity. A normalized key function replaces it.

    Required fields: schema, block, proof, entries, entry_context, hints,
    imports, toolchain, search. Each named list uses {name, source}, where
    source is {sha256, path?}. toolchain and search are nonempty JSON objects.
    The search identity must bind provider/tactic code and search options.
    """
    fields = {'schema', 'block', 'proof', 'entries', 'entry_context', 'hints',
              'imports', 'toolchain', 'search'}
    if set(spec) != fields or spec['schema'] != KEY_SCHEMA:
        raise ValueError('The cache key specification has unsupported fields.')
    if not isinstance(spec['block'], str) or not spec['block']:
        raise ValueError('The cache key has no block identity.')
    identity = {name: spec[name] for name in ('schema', 'block')}
    identity['proof'] = source_identity(spec['proof'])
    for name in ('entries', 'entry_context', 'hints', 'imports'):
        identity[name] = named_sources(spec[name], name)
    for name in ('toolchain', 'search'):
        if not isinstance(spec[name], dict) or not spec[name]:
            raise ValueError(f'The cache key has no {name} identity.')
        identity[name] = deepcopy(spec[name])
    identity['key_function'] = 'raw-bindings-v1'
    return identity


def build_key(spec, key_function=None):
    """Hash the normalized JSON identity returned by key_function(spec).

    The replacement function owns normalization. It must return a nonempty
    block string and a versioned key_function string beside its semantic
    inputs. Evidence paths and execution metadata belong outside this return
    value. The default raw binding function is provisional, not the released
    normalized specification. Storage never calls the key function again.
    """
    identity = (key_function or bound_identity)(deepcopy(spec))
    if not isinstance(identity, dict):
        raise ValueError('The key function did not return a JSON object.')
    for name in ('block', 'key_function'):
        if not isinstance(identity.get(name), str) or not identity[name]:
            raise ValueError(f'The normalized identity has no {name}.')
    return {'schema': KEY_SCHEMA, 'sha256': semantic_digest(identity),
            'identity': identity}


def validate_key(key):
    if set(key) != {'schema', 'sha256', 'identity'} or key['schema'] != KEY_SCHEMA:
        raise ValueError('The cache key has unsupported fields.')
    identity = key['identity']
    if not isinstance(identity, dict) or any(not isinstance(identity.get(name), str) or
                                            not identity[name] for name in ('block', 'key_function')):
        raise ValueError('The cache key has no normalized identity.')
    expected = semantic_digest(identity)
    if checked_digest(key['sha256']) != expected:
        raise ValueError('The cache key digest differs from its identity.')


def references(value):
    """Find source, object, and ordinary file bindings in a native result."""
    rows = []
    if isinstance(value, dict):
        if isinstance(value.get('path'), str) and 'sha256' in value:
            rows.append({'path': value['path'], 'sha256': value['sha256']})
        for name in ('source', 'object'):
            if isinstance(value.get(name), str) and name + '_sha256' in value:
                rows.append({'path': value[name], 'sha256': value[name + '_sha256']})
        for child in value.values():
            rows.extend(references(child))
    elif isinstance(value, list):
        for child in value:
            rows.extend(references(child))
    return rows


def validate_result(result):
    if result.get('phase') != 'native' or not isinstance(result.get('success'), bool):
        raise ValueError('The result is not a completed native observation.')
    if result.get('shared_infrastructure_failure') or result.get('observer_failure'):
        raise ValueError('An infrastructure failure cannot enter the result cache.')
    state = result.get('complete_state')
    if not isinstance(state, dict) or not state.get('path') or not state.get('sha256'):
        raise ValueError('The result has no complete final state.')
    if state.get('state_source') not in {'successful_command_returned_state', 'returned_error_state'}:
        raise ValueError('A pre-call fallback cannot enter the result cache.')
    groups = result.get('group_counts')
    names = {'active', 'focus_frames', 'frame_goals', 'shelves', 'given_up'}
    if not isinstance(groups, dict) or set(groups) != names:
        raise ValueError('The result does not retain all goal groups.')
    if any(type(n) is not int or n < 0 for n in groups.values()):
        raise ValueError('The result has invalid goal counts.')
    if result['success']:
        if any(groups.values()):
            raise ValueError('A closed result retains goals.')
        receipts = result.get('native_receipts', {})
        if not receipts or any(not row.get('compile_file_success') or
                               row.get('verification_method') != 'module_m' or
                               row.get('assumptions') != [] for row in receipts.values()):
            raise ValueError('A closed result lacks kernel verification.')
        if any(Path(row.get('object', '')).suffix != '.vo' for row in receipts.values()):
            raise ValueError('A closed result lacks a full proof object.')
    elif result.get('status') != 'native_open' or result.get('normal_tactic_return') is not True or result.get('proof_finished') is not False:
        raise ValueError('An open outcome lacks a normal tactic return.')


def validate_state(result):
    state = json.loads(Path(result['complete_state']['path']).read_text())
    names = {'goals', 'stack', 'shelf', 'given_up'}
    if not isinstance(state, dict) or not names.issubset(state):
        raise ValueError('The cached state omits a goal group.')
    if any(not isinstance(state[name], list) for name in names):
        raise ValueError('The cached state has an invalid goal group.')
    kernel = state.get('kernel_groups')
    if not isinstance(kernel, dict) or not names.issubset(kernel):
        raise ValueError('The cached state omits a kernel group.')
    if any(not isinstance(kernel[name], list) for name in names):
        raise ValueError('The cached state has an invalid kernel group.')
    groups = result['group_counts']
    for actual, reported in [('goals', 'active'), ('stack', 'focus_frames'),
                             ('shelf', 'shelves'), ('given_up', 'given_up')]:
        if len(state[actual]) != groups[reported]:
            raise ValueError('The retained state differs from its reported group counts.')
    frames = state['stack']
    if any(not isinstance(frame, list) or len(frame) != 2 or
           any(not isinstance(side, list) for side in frame) for frame in frames):
        raise ValueError('The retained state has an invalid focus frame.')
    if sum(len(left) + len(right) for left, right in frames) != groups['frame_goals']:
        raise ValueError('The retained focus frames differ from their reported count.')
    if result['success'] and any(kernel[name] for name in names):
        raise ValueError('A closed result retains kernel goals.')
    # An open hit reuses only the exact attempt's verdict. The retained groups
    # are diagnostics. The cache never reconstructs a proof state or resumes it.


def relocated(value, paths):
    if isinstance(value, dict):
        return {name: relocated(child, paths) for name, child in value.items()}
    if isinstance(value, list):
        return [relocated(child, paths) for child in value]
    return paths.get(value, value) if isinstance(value, str) else value


def store(cache_dir, key, result_path, artifacts=(), *, purpose='exploration'):
    """Copy evidence atomically. artifacts is an iterable of file bindings."""
    if not enabled(purpose):
        return {'cache_status': 'disabled'}
    validate_key(key)
    raw = Path(result_path).read_bytes()
    result = json.loads(raw)
    validate_result(result)
    validate_state(result)
    if result['block'] != key['identity']['block']:
        raise ValueError('The result names another block.')
    if key['identity']['key_function'] == 'raw-bindings-v1':
        for receipt in result.get('native_receipts', {}).values():
            if receipt.get('source_sha256') != key['identity']['proof']['sha256']:
                raise ValueError('The native proof source differs from the cache key.')
    if key['identity']['key_function'] == 'zesu-proof-attempt-v1':
        expected = key['identity']['proof_source_sha256']
        receipts = result.get('native_receipts', {})
        if receipts:
            if any(row.get('source_sha256') != expected for row in receipts.values()):
                raise ValueError('The verified source differs from the normalized recipe.')
        elif result.get('proof_source_sha256') != expected:
            raise ValueError('The open source differs from the normalized recipe.')
    root = Path(cache_dir)
    root.mkdir(parents=True, exist_ok=True)
    target = root / key['sha256']
    if target.exists():
        return {'cache_status': 'already-stored', 'key': key['sha256'],
                'manifest': str(target / 'MANIFEST.json')}
    staging = Path(tempfile.mkdtemp(prefix='.cache-', dir=root))
    try:
        blobs = staging / 'files'
        blobs.mkdir()
        retained = []
        for row in references(result) + list(artifacts):
            source_identity(row)
            sha = row['sha256']
            destination = blobs / sha
            if not destination.exists():
                clone_copy.copyfile(row['path'], destination)
            if digest(destination) != sha:
                raise ValueError('A cache artifact changed during its copy.')
            retained.append({'original_path': row['path'], 'sha256': sha})
        clone_copy.copy2(result_path,staging / 'RESULT.json')
        receipt = {'schema': SCHEMA, 'key': key,
                   'result_sha256': hashlib.sha256(raw).hexdigest(),
                   'artifacts': retained}
        if key['identity']['key_function'] == 'zesu-proof-attempt-v1':
            from proof_cache_key import ARTIFACT_SCHEMA, artifact_key
            manifest = {'schema': ARTIFACT_SCHEMA, 'attempt_key': key['sha256'],
                        'status': 'closed' if result['success'] else 'open',
                        'acceptance': key['identity']['acceptance'],
                        'files': [{'id': 'sha256:' + sha, 'sha256': sha}
                                  for sha in sorted({row['sha256'] for row in retained})]}
            receipt.update(artifact_manifest=manifest, artifact_key=artifact_key(manifest))
        (staging / 'MANIFEST.json').write_bytes(encoded(receipt))
        try:
            os.rename(staging, target)
        except OSError:
            if not target.is_dir():
                raise
        return {'cache_status': 'stored', 'key': key['sha256'],
                'manifest': str(target / 'MANIFEST.json')}
    finally:
        if staging.exists():
            shutil.rmtree(staging)


def _read_entry(cache_dir, key):
    """Validate retained evidence. This internal operation permits no reuse."""
    validate_key(key)
    target = Path(cache_dir) / key['sha256']
    if not target.exists():
        return None
    receipt = json.loads((target / 'MANIFEST.json').read_text())
    if receipt['schema'] != SCHEMA or receipt['key'] != key:
        raise ValueError('The cached identity differs from its requested key.')
    if key['identity']['key_function'] == 'zesu-proof-attempt-v1':
        from proof_cache_key import artifact_key
        manifest = receipt.get('artifact_manifest')
        if not manifest or manifest.get('attempt_key') != key['sha256'] or artifact_key(manifest) != receipt.get('artifact_key'):
            raise ValueError('The cached artifact identity changed.')
        if {row['sha256'] for row in manifest['files']} != {row['sha256'] for row in receipt['artifacts']}:
            raise ValueError('The cached artifact manifest omits retained evidence.')
    if digest(target / 'RESULT.json') != receipt['result_sha256']:
        raise ValueError('The cached result changed.')
    paths = {}
    for row in receipt['artifacts']:
        path = target / 'files' / checked_digest(row['sha256'])
        if digest(path) != row['sha256']:
            raise ValueError('A cached artifact changed.')
        if row['original_path'] in paths and paths[row['original_path']] != str(path):
            raise ValueError('One cached source path has different identities.')
        paths[row['original_path']] = str(path)
    result = json.loads((target / 'RESULT.json').read_text())
    validate_result(result)
    if result['block'] != key['identity']['block']:
        raise ValueError('The cached result names another block.')
    if any(row['path'] not in paths for row in references(result)):
        raise ValueError('The cache does not retain all result bindings.')
    result = relocated(result, paths)
    validate_state(result)
    return {'cache_status': 'cached', 'key': key['sha256'],
            'result': result,
            'cached_verdict': {'status': 'closed' if result['success'] else 'open',
                               'accepted': result['success']},
            'reuse_kind': 'closed-proof-evidence' if result['success'] else 'open-verdict',
            'state_reconstruction_supported': False,
            'residual_role': 'empty-final-state' if result['success'] else 'diagnostic',
            'original_result': str(target / 'RESULT.json'),
            'manifest': str(target / 'MANIFEST.json'),
            'fresh_search_cpu_seconds': 0,
            'historical_cpu': result.get('CPU'), 'paths': paths}


def evict(cache_dir, key, reason):
    """Remove an active entry while retaining the failed evidence for audit."""
    root = Path(cache_dir)
    target = root / key['sha256']
    archive = root / '.defects' / (key['sha256'] + '-' + uuid.uuid4().hex)
    archive.parent.mkdir(parents=True, exist_ok=True)
    try:
        os.rename(target, archive)
    except FileNotFoundError:
        archive = None
    record = {'schema': 'entry-chain.cache-defect.v1', 'key': key['sha256'],
              'reason': reason, 'time_ns': time.time_ns(),
              'evicted_entry': str(target), 'archive': str(archive) if archive else None}
    receipt = archive / 'DEFECT.json' if archive else root / '.defects' / (uuid.uuid4().hex + '.json')
    receipt.write_bytes(encoded(record))
    record['receipt'] = str(receipt)
    return record


def checked_closed_verdict(hit, check):
    if not isinstance(check, dict) or check.get('success') is not True or check.get('checked_key') != hit['key']:
        return False
    if check.get('method') == 'coqchk':
        return check.get('recursive') is True and check.get('admitted_modules') == []
    if check.get('method') == 'load-exact-statement':
        expected = hit['result'].get('statement_sha256')
        return bool(expected and check.get('statement_sha256') == expected and
                    check.get('assumptions') == [] and check.get('vo_loaded') is True)
    return False


def lookup(cache_dir, key, *, verify_closed=None, on_defect=None, purpose='exploration'):
    """Check every closed hit with the current kernel before permitting reuse.

    The adapter supplies canonical admission and current dependencies to its
    verifier. A failed check evicts the entry. on_defect records the mismatch,
    then None instructs the adapter to run fresh. No proof search runs here.
    """
    if not enabled(purpose):
        return None
    validate_key(key)
    try:
        hit = _read_entry(cache_dir, key)
    except (OSError, ValueError, KeyError, TypeError) as error:
        defect = evict(cache_dir, key, 'integrity: ' + str(error))
        if on_defect is None:
            raise CacheDefect(defect) from error
        on_defect(defect)
        return None
    if hit is None:
        return None
    if hit['result']['success']:
        if not callable(verify_closed):
            raise ValueError('A closed cache hit requires a current kernel verifier.')
        try:
            check = verify_closed(hit)
            valid = checked_closed_verdict(hit, check)
            reason = 'kernel check rejected the cached proof'
        except Exception as error:
            valid, reason = False, 'kernel check raised: ' + str(error)
        if not valid:
            defect = evict(cache_dir, key, reason)
            if on_defect is None:
                raise CacheDefect(defect)
            on_defect(defect)
            return None
        hit['kernel_recheck'] = check
    else:
        hit['cache_status'] = 'cached open (not re-run)'
    return hit


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('operation', choices=['key', 'lookup', 'store'])
    parser.add_argument('--spec', type=Path, required=True)
    parser.add_argument('--cache', type=Path)
    parser.add_argument('--result', type=Path)
    parser.add_argument('--artifacts', type=Path)
    args = parser.parse_args()
    key = build_key(json.loads(args.spec.read_text()))
    if args.operation == 'key':
        value = key
    else:
        if args.cache is None:
            parser.error('--cache is required.')
        if args.operation == 'lookup':
            value = lookup(args.cache, key)
        else:
            if args.result is None:
                parser.error('--result is required.')
            artifacts = json.loads(args.artifacts.read_text()) if args.artifacts else []
            value = store(args.cache, key, args.result, artifacts)
    print(json.dumps(value, sort_keys=True))


if __name__ == '__main__':
    main()
