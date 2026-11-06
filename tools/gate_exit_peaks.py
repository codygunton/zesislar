"""Use the last released guard measurement for an unchanged gate run kind."""
from pathlib import Path
import subprocess
import hashlib
import json
import os
import shutil

from block.harness.code.entry_chain import binding, read_bound
from block.harness.code.admission_memory import ScopeReader

SCHEMA = 'zesu.guard.gate-exit.v1'
GIB = 1024 ** 3


def toolchain():
    """Resolve the toolchain through the same opam switch as the Makefile."""
    switch = os.environ.get('OPAM_SWITCH', os.environ.get('ISLARIS_REPO', str(Path.home()/'islaris')))
    opam = shutil.which('opam')
    if opam is None:
        return None
    try:
        paths = subprocess.check_output([opam, 'exec', '--switch='+switch, '--',
            '/bin/sh', '-c', 'command -v coqc; command -v dune'], text=True).splitlines()
        if len(paths) != 2 or any(not Path(path).is_absolute() for path in paths):
            return None
        return {'opam': binding(Path(opam).resolve()), 'switch': switch,
                **{name: binding(Path(path).resolve()) for name, path in zip(('coqc','dune'),paths)}}
    except (OSError, subprocess.CalledProcessError):
        return None


def code_identity(workspace):
    """Bind workload bytes, not revision IDs or prose-only revisions."""
    workspace = Path(workspace)
    paths = subprocess.check_output(['git', '-C', str(workspace), 'ls-files', '-z'], text=True).split('\0')
    rows = []
    for name in sorted(path for path in paths if path):
        path = workspace/name
        if path.suffix.lower() in ('.md', '.rst') or path.name in ('.gitignore', '.gitattributes', 'LICENSE'):
            continue
        if not path.is_file():
            return None
        rows.append((name, hashlib.sha256(path.read_bytes()).hexdigest()))
    tools = toolchain()
    if tools is None:
        return None
    from gate_scope import tools_digest
    return {'workload_sha256': hashlib.sha256(json.dumps(rows).encode()).hexdigest(),
            'tools_tree_sha256': tools_digest(workspace),
            'toolchain': tools,
            'environment': {key: os.environ.get(key) for key in ('COQC', 'DUNE_PROFILE', 'ZESU_GATE_MAX_JOBS', 'ZESU_FAST_MAX_JOBS', 'ZESU_MAX_COQC', 'ZESU_WRITER_MAX_COQC', 'ZESU_GATE_JOBS', 'DUNE_JOBS', 'AGENT_JOBS', 'COQFLAGS', 'OCAMLPATH')}}


def sample(aggregate, request, actor, *, reader=None):
    """Read the live owned aggregate after its payload exits, before cleanup."""
    reader = ScopeReader() if reader is None else reader
    identity = reader.directory(aggregate)
    reader.scope(aggregate, actor, request['owner'], expected=identity)
    limit = request['policy']['physical_fence_bytes']
    guard = request['guard_source']
    if reader.guard_source(guard['path'], guard['sha256']) != guard:
        raise ValueError('The gate measurement guard identity changed.')
    if (int((aggregate/'memory.max').read_text()) != limit
            or (aggregate/'memory.swap.max').read_text().strip() != '0'):
        raise ValueError('The gate measurement fence changed.')
    peak = int((aggregate/'memory.peak').read_text())
    if peak <= 0 or reader.directory(aggregate) != identity:
        raise ValueError('The gate measurement aggregate changed.')
    return {'schema': SCHEMA, 'role': 'correctness-gate', 'run_kind': request['target'],
            'owner': request['owner'], 'actor': actor, 'guard_source': guard,
            'aggregate': {'path': str(aggregate), 'device': identity[0], 'inode': identity[1]},
            'physical_fence_bytes': limit, 'memory_peak_bytes': peak}


def endorse(output, request, ledger, *, closed):
    """Endorse only the normal exact-claim release path, under its ledger lock."""
    result_path = output/'RESULT.json'
    if (not result_path.is_file() or request.get('code_identity') is None
            or request['command'] != ['make','--no-print-directory','_'+request['target']]):
        return
    result = read_bound(binding(result_path))
    measured = result.get('guard_exit')
    if not isinstance(measured, dict):
        return
    key = request['policy']['claim_key']
    if (measured.get('schema') != SCHEMA or measured.get('role') != 'correctness-gate'
            or measured.get('run_kind') != request['target']
            or measured.get('owner') != request['owner']
            or measured.get('guard_source') != request['guard_source']
            or measured.get('physical_fence_bytes') != request['policy']['physical_fence_bytes']
            or measured.get('memory_peak_bytes') != result.get('aggregate_peak_bytes')
            or result.get('success') is not True or result.get('exit_code') != 0
            or result.get('code_identity_after') != request['code_identity']
            or not closed or ledger['fixed_claims'].get(key) != 0
            or ledger['correctness_gate_releases'][key]['owner'] != request['owner']):
        raise ValueError('The gate exit lacks its exact released measurement.')
    ledger.setdefault('gate_exit_peaks', []).append({
        'request': binding(output/'REQUEST.json'), 'result': binding(result_path),
        'closure': binding(output/'CLOSURE.json'), 'run_kind': request['target'],
        'code_identity': request['code_identity'], 'claim_key': key})


def latest(ledger, target, command, limit, identity, *, closed, guard_reader=None):
    """Invalid latest matching evidence keeps the existing admission default."""
    if identity is None or command != ['make','--no-print-directory','_'+target]:
        return None
    reader = ScopeReader() if guard_reader is None else guard_reader
    for entry in reversed(ledger.get('gate_exit_peaks', [])):
        if (not isinstance(entry, dict) or entry.get('run_kind') != target
                or entry.get('code_identity') != identity):
            continue
        try:
            request = read_bound(entry['request'])
            result = read_bound(entry['result'])
            closure = read_bound(entry['closure'])
            policy, owner = request['policy'], request['owner']
            key = entry['claim_key']
            measured = result['guard_exit']
            release = ledger['correctness_gate_releases'][key]
            batch = closure['batch']
            if (request['target'] != target or request['command'] != command
                    or request['code_identity'] != identity or result.get('code_identity_after') != identity or policy['claim_key'] != key
                    or policy['physical_fence_bytes'] != limit
                    or ledger['correctness_gate_owners'][key] != owner
                    or ledger['fixed_claims'][key] != 0 or release['owner'] != owner
                    or release['bytes'] != policy['claim_bytes'] or release['released'] is not True
                    or release['receipt_sha256'] != entry['request']['sha256']
                    or closure['all_owned_actors_closed'] is not True or not closed(batch)
                    or not closed({'actors': [owner]})
                    or measured['actor'] not in batch['actors']
                    or measured['aggregate']['path'] not in batch['aggregate_paths']
                    or Path(measured['aggregate']['path']).exists()
                    or measured['owner'] != owner or measured['schema'] != SCHEMA
                    or measured['role'] != 'correctness-gate' or measured['run_kind'] != target
                    or measured['physical_fence_bytes'] != limit
                    or measured['guard_source'] != request['guard_source']
                    or reader.guard_source(request['guard_source']['path'], request['guard_source']['sha256']) != request['guard_source']
                    or result['success'] is not True or type(result['exit_code']) is not int or result['exit_code'] != 0
                    or type(result['completed_ns']) is not int or result['completed_ns'] <= 0
                    or type(measured['memory_peak_bytes']) is not int or measured['memory_peak_bytes'] <= 0
                    or measured['memory_peak_bytes'] != result['aggregate_peak_bytes']):
                return None
            return {'reason': 'last_released_guard_gate_peak', 'family': target,
                    'record': entry, 'aggregate_peak_bytes': measured['memory_peak_bytes'],
                    'claim_bytes': max(GIB, (3*measured['memory_peak_bytes']+1)//2),
                    'physical_fence_bytes': limit,
                    'measurement_provenance': result.get('cache_provenance'),
                    'qualification': 'Last guard-recorded peak for this unchanged source tree and run kind. Cache state remains qualified.'}
        except (AttributeError, KeyError, OSError, TypeError, ValueError):
            return None
    return None
