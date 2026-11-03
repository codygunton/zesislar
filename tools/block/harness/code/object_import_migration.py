"""Authenticate legacy objects with their own Rocq dependency digests.

Migration records do not claim a new physical compilation. Accepted origins
remain explicit, and every recorded import (including installed libraries)
must pass the pinned Rocq digest comparison again before reuse.
"""
import argparse
from contextlib import contextmanager
from contextvars import ContextVar
from copy import deepcopy
import json
import os
from pathlib import Path
import resource
import subprocess
import time

from entry_chain import binding, read_bound
from installed_mappings import InstalledMappings
from source_context import compilation
from binding_cache import identity as file_identity


SCHEMA = 'entry-chain.object-import-migration.v1'
POLICY = Path(__file__).with_name('OBJECT-IMPORT-MIGRATION-ORIGINS.json')
if not POLICY.is_file():
    POLICY = Path(__file__).resolve().parents[1] / 'policies/OBJECT-IMPORT-MIGRATION-ORIGINS.json'
_BATCH = ContextVar('object_migration_batch', default=None)


@contextmanager
def batch():
    """Share only identity-checked metadata within one authenticated operation."""
    active = _BATCH.get()
    if active is not None:
        yield active
        return
    active = {'summaries': {}, 'checks': {}, 'resolvers': {}, 'records': {},
              'context': None, 'inspector_calls': 0, 'inspector_hits': 0}
    token = _BATCH.set(active)
    try:
        yield active
    finally:
        _BATCH.reset(token)


def bound_record(reference):
    active = _BATCH.get()
    if active is None:
        return read_bound(reference)
    path = Path(reference['path'])
    key = (os.getpid(), str(path), reference['sha256'], file_identity(path))
    if binding(path) != reference:
        raise ValueError('A migration input binding changed.')
    if key not in active['records']:
        active['records'][key] = read_bound(reference)
    return active['records'][key]


def normalized(flags, workspace):
    return [word.replace(str(workspace), '{workspace}') for word in flags]


def identity(path):
    return file_identity(Path(path))


def inspector_spec(policy):
    build = bound_record(policy['inspector_build'])
    binary = build['binary']
    bound_record(build['API_review'])
    if (binary['sha256'] != policy['inspector_binary_sha256'] or
            build['source']['sha256'] != policy['inspector_source_sha256'] or
            binding(binary['path']) != binary):
        raise ValueError('The migration inspector differs from its approved build.')
    return binary


def run_inspector(policy, objects, checks):
    binary = inspector_spec(policy)
    paths = sorted({str(Path(path).resolve()) for path in objects})
    before = {path: (binding(path), identity(path)) for path in paths}
    request = {'schema': 'rocq.vo-inspection.request.v1', 'objects': paths, 'checks': checks}
    run = subprocess.run([binary['path']], input=json.dumps(request), text=True,
                         capture_output=True, check=False)
    if run.returncode:
        raise ValueError('The migration inspector refused: ' + run.stderr.strip())
    result = json.loads(run.stdout)
    if (result.get('schema') != 'rocq.vo-inspection.v1' or
            result.get('vo_version') != 81999 or
            result.get('coq_version') != '8.19.2+lsp'):
        raise ValueError('The migration inspector returned another schema or toolchain.')
    for path, previous in before.items():
        if previous != (binding(path), identity(path)):
            raise ValueError('An inspected object changed during migration.')
    return result


def inspector(policy, objects, checks):
    active = _BATCH.get()
    if active is None:
        return run_inspector(policy, objects, checks)
    binary = inspector_spec(policy)
    paths = sorted({str(Path(path).resolve()) for path in objects})
    keys = {path: (active['context'], policy['inspector_build']['sha256'], binary['sha256'],
                   path, binding(path)['sha256'], identity(path)) for path in paths}
    check_keys = [(keys[row['owner']], keys[row['object']], row['module']) for row in checks]
    missing_checks = [row for row, key in zip(checks, check_keys) if key not in active['checks']]
    missing_paths = {path for path, key in keys.items() if key not in active['summaries']}
    for row in missing_checks:
        missing_paths.update([row['owner'], row['object']])
    if missing_paths:
        result = run_inspector(policy, missing_paths, missing_checks)
        active['inspector_calls'] += 1
        for row in result['objects']:
            active['summaries'][keys[row['path']]] = row
        for row in result['checks']:
            active['checks'][(keys[row['owner']], keys[row['object']], row['module'])] = row
    else:
        active['inspector_hits'] += 1
    for path, key in keys.items():
        if key[-2:] != (binding(path)['sha256'], identity(path)):
            raise ValueError('A cached inspected object changed.')
    return deepcopy({'schema': 'rocq.vo-inspection.v1', 'vo_version': 81999,
        'coq_version': '8.19.2+lsp',
        'objects': [active['summaries'][keys[path]] for path in paths],
        'checks': [active['checks'][key] for key in check_keys]})


def origin(policy, reference, module, source, obj, compiler, flags, workspace):
    selected = [row for row in policy['origins'] if row['binding'] == reference]
    if len(selected) != 1:
        raise ValueError('The migration origin is not an approved publication.')
    authority = selected[0]
    publication = bound_record(reference)
    if authority['kind'] == 'accepted-correctness-gate-objects':
        from gate_object_origin import selected_origin
        return selected_origin(authority, reference, module, source, obj, compiler, flags, workspace, bound_record)
    if authority['kind'] == 'accepted-closed-compilations':
        from closed_compilation_origin import selected_origin
        return selected_origin(authority, reference, module, source, obj, compiler, flags, workspace, bound_record)
    if authority['kind'] not in {'accepted-supplier', 'accepted-ready'}:
        raise ValueError('The migration origin kind is unsupported.')
    if authority['kind'] == 'accepted-supplier' and publication['ready'] != authority['ready']:
        raise ValueError('The supplier names another accepted runtime.')
    ready = bound_record(authority['ready'])
    if authority['kind'] == 'accepted-ready':
        selection = bound_record(authority['selection'])
        guards = authority['selection_guards']
        if 'module_allowlist' in authority and module not in authority['module_allowlist']:
            raise ValueError('The selected READY does not authorize this module origin.')
        if (reference != authority['ready'] or not guards or
                not any(row['path'] == reference['path'] and row['sha256'] == reference['sha256']
                        for row in selection['rows']) or
                selection['recorded_expected_objects'] != guards):
            raise ValueError('The accepted READY lacks its exact authorized selection.')
        inputs = {row['path']: row for row in ready['bindings']}
        root = Path(ready['prepared_workspace']).resolve()
        def mapped(name):
            relative = ready['proof_runtime']['module_files'].get(name)
            if relative is None:
                raise ValueError('The accepted READY lacks a module mapping: ' + name)
            selected = (root / relative).resolve()
            if not selected.is_relative_to(root):
                raise ValueError('The selected READY module is not owned: ' + name)
            source_row, object_row = inputs.get(str(selected)), inputs.get(str(selected.with_suffix('.vo')))
            if source_row is None or object_row is None:
                raise ValueError('The accepted READY lacks bound source/object identities: ' + name)
            return {'module': name, 'source': source_row, 'object': object_row}
        for name, expected in guards.items():
            if mapped(name)['object']['sha256'] != expected:
                raise ValueError('The accepted READY differs from a selected frozen marker.')
        rows = [mapped(module)]
    else:
        rows = [row for row in publication['modules'] if row['module'] == module]
    if len(rows) != 1:
        raise ValueError('The supplier lacks one exact module binding.')
    row = rows[0]
    old_workspace = Path(ready['prepared_workspace']).resolve()
    old_source = Path(row['source']['path']).resolve()
    if (not old_source.is_relative_to(old_workspace) or
            old_source.relative_to(old_workspace) != source.resolve().relative_to(workspace) or
            Path(row['object']['path']).resolve() != old_source.with_suffix('.vo') or
            row['source']['sha256'] != binding(source)['sha256'] or
            row['object']['sha256'] != binding(obj)['sha256'] or
            compiler not in ready['bindings'] or binding(compiler['path']) != compiler or
            normalized(ready['physical_flags'], old_workspace) != normalized(flags, workspace)):
        raise ValueError('The migrated object differs from its accepted origin inputs.')
    # The old source remains an authenticated input. Source-context changes cannot
    # retroactively claim that a legacy object used the new physical flags.
    effective = compilation(flags, binding(source))['physical_flags']
    if normalized(effective, workspace) != normalized(ready['physical_flags'], old_workspace):
        raise ValueError('The migrated object requires another compiler source context.')
    evidence, label = [], ('inherited-from-accepted-READY' if
                          authority['kind'] == 'accepted-ready' else 'inherited-from-accepted-supplier')
    individual = authority.get('individual_receipts', {}).get(module, [])
    dependency = authority.get('dependency_receipts', {}).get(module, [])
    if individual:
        receipt = bound_record(individual[0])
        if (receipt.get('successful_compilation') is not True or
                receipt.get('tool_result', {}).get('success') is not True or
                receipt['source']['sha256'] != row['source']['sha256'] or
                receipt['object']['sha256'] != row['object']['sha256'] or
                receipt['compiler'] != compiler):
            raise ValueError('The individual compilation receipt differs from the origin.')
        physical = bound_record(receipt['physical_result'])
        inputs = bound_record(physical['input'])
        if (physical.get('returncode') != 0 or
                physical.get('output_validation', {}).get('success') is not True or
                physical.get('compiler_outputs', {}).get('object', {}).get('binding') != receipt['object'] or
                inputs.get('source') != receipt['source'] or inputs.get('compiler') != compiler):
            raise ValueError('The individual compilation lacks its physical output binding.')
        evidence, label = [individual[0]], 'individual-accepted-compilation'
    elif dependency:
        receipt = bound_record(dependency[0])
        if (receipt.get('result', {}).get('success') is not True or
                receipt.get('source_sha256') != row['source']['sha256'] or
                receipt.get('object_sha256') != row['object']['sha256']):
            raise ValueError('The dependency receipt differs from the accepted origin.')
        evidence, label = [dependency[0]], 'successful-dependency-from-accepted-runtime'
    return {'kind': label, 'publication': reference, 'ready': authority['ready'],
            'original_receipts': evidence}, effective


def comparisons(policy, module, obj, flags, coqdep, *, recorded=None, supplier=None):
    active = _BATCH.get()
    context = (tuple(flags), coqdep['path'], coqdep['sha256'],
               binding(Path(coqdep['path']).with_name('coqc'))['sha256'])
    if active is not None:
        active['context'] = context
    owner = str(obj.resolve())
    initial = inspector(policy, [owner], [])
    summaries = [row for row in initial['objects'] if row['path'] == owner]
    if len(summaries) != 1 or summaries[0]['module'] != module:
        raise ValueError('The migrated object has another canonical module name.')
    required = [row['module'] for row in summaries[0]['imports']]
    if len(set(required)) != len(required):
        raise ValueError('The migrated object repeats a dependency name.')
    if binding(coqdep['path']) != coqdep:
        raise ValueError('The migration coqdep binding changed.')
    key = (context, json.dumps(supplier, sort_keys=True))
    shared = active['resolvers'].get(key) if active is not None else None
    resolver = None
    if shared is not None:
        candidate, inventory = shared
        if candidate.shared_cache.inventory(candidate) == inventory:
            resolver = candidate
    if resolver is None:
        resolver = InstalledMappings(flags, coqdep=Path(coqdep['path']), supplier=supplier)
        if active is not None and resolver.shared_cache is not None:
            inventory = resolver.shared_cache.inventory(resolver)
            if inventory is not None:
                active['resolvers'][key] = (resolver, inventory)
    rows, checks, aliases = [], [], []
    for name in required:
        # The batch already checked the complete directory inventory. Every
        # selected file receives a fresh identity/hash check below.
        cached = resolver.resolutions if active is not None else {}
        resolved = cached.get(name) if isinstance(cached, dict) else None
        if resolved is None:
            resolved = resolver.resolution(name)
        selected = Path(resolved['object']).resolve()
        # A physical path can occur under overlapping mapping prefixes. The
        # inspector checks the object's own canonical identity for every check.
        if resolved['canonical'] != name:
            aliases.append({'requested_module': name, 'resolver_canonical': resolved['canonical'],
                            'physical_object': binding(selected)})
        rows.append({'module': name, 'object': binding(selected)})
        checks.append({'owner': owner, 'module': name, 'object': str(selected)})
    if recorded is not None and rows != recorded:
        raise ValueError('A recorded dependency differs from the resolved current bank.')
    result = inspector(policy, [owner, *(row['object']['path'] for row in rows)], checks)
    actual = result['checks']
    if (len(actual) != len(required) or {row['module'] for row in actual} != set(required) or
            any(row.get('compatible') is not True for row in actual) or
            any(row['owner'] != owner or row['object'] != check['object'] or
                row['module'] != check['module'] for row, check in zip(actual, checks))):
        raise ValueError('The complete Rocq dependency digest comparison refused.')
    result['resolver_aliases'] = aliases
    return rows, result


def origin_context(policy, accepted):
    if accepted.get('kind') == 'individual-object-from-accepted-correctness-gate':
        from gate_object_origin import context
        authority = next(row for row in policy['origins'] if row['binding'] == accepted['publication'])
        return context(authority, accepted['publication'], bound_record)[0]
    if 'closed_runtime' in accepted:
        from closed_compilation_origin import context
        authority = next(row for row in policy['origins'] if row['binding'] == accepted['publication'])
        return context(authority, accepted['publication'], bound_record)[0]
    return bound_record(accepted['ready'])


def create(reference, module, source, obj, compiler, flags, workspace):
    policy = json.loads(POLICY.read_text())
    workspace, source, obj = Path(workspace).resolve(), Path(source), Path(obj)
    accepted, effective = origin(policy, reference, module, source, obj, compiler, flags, workspace)
    ready = origin_context(policy, accepted)
    coqdep = next((row for row in ready['bindings']
                   if row['path'] == str(Path(compiler['path']).with_name('coqdep'))), None)
    if coqdep is None:
        raise ValueError('The accepted runtime lacks the pinned coqdep binding.')
    rows, result = comparisons(policy, module, obj, effective, coqdep, supplier=reference)
    recorded_flags = normalized(effective, workspace)
    if accepted.get('kind') == 'individual-object-from-accepted-correctness-gate':
        from gate_object_origin import normalize_flags
        recorded_flags = normalize_flags(effective, workspace)
    receipt = {'schema': SCHEMA, 'origin': accepted, 'module': module,
            'owned_workspace': str(workspace), 'source': binding(source), 'object': binding(obj),
            'compiler': compiler, 'normalized_flags': recorded_flags,
            'inspector_build': policy['inspector_build'], 'coqdep': coqdep,
            'imported_objects': rows, 'comparison': result,
            'qualification': 'Authenticated migration. No new physical compilation or proof check.'}
    if accepted.get('kind') == 'individual-object-from-accepted-correctness-gate':
        receipt['gate_identity_observations'] = ready['gate_identity_observations'][module]
        receipt['gate_build_observations'] = ready['gate_build_observations']
    return receipt


def validate(reference, module, source, obj, compiler, flags, workspace):
    receipt = read_bound(reference)
    return _validate_document(receipt, module, source, obj, compiler, flags, workspace)


def _validate_document(receipt, module, source, obj, compiler, flags, workspace):
    """Validate a receipt document already authenticated by read_bound."""
    policy = json.loads(POLICY.read_text())
    workspace, source, obj = Path(workspace).resolve(), Path(source), Path(obj)
    accepted, effective = origin(policy, receipt['origin']['publication'], module,
                                 source, obj, compiler, flags, workspace)
    old_workspace = Path(receipt['owned_workspace']).resolve()
    gate = accepted.get('kind') == 'individual-object-from-accepted-correctness-gate'
    recorded_flags = normalized(effective, workspace)
    if gate:
        from gate_object_origin import normalize_flags, relocate
        recorded_flags = normalize_flags(effective, workspace)
        publication = bound_record(accepted['publication'])
        prior_source = Path(receipt['source']['path']).resolve()
        expected_source = (Path(publication['build_root']) /
                           Path(*Path(bound_record(publication['resolution_runtime'])['proof_runtime']['module_files'][module]).parts[1:]))
        path_matches = (prior_source == expected_source and
                        old_workspace == Path(publication['build_root']).resolve() and
                        Path(receipt['object']['path']) == expected_source.with_suffix('.vo'))
    else:
        path_matches = (Path(receipt['source']['path']).resolve().relative_to(old_workspace) ==
                        source.resolve().relative_to(workspace))
    if (receipt.get('schema') != SCHEMA or receipt['origin'] != accepted or
            receipt['module'] != module or receipt['compiler'] != compiler or
            receipt['source']['sha256'] != binding(source)['sha256'] or
            receipt['object']['sha256'] != binding(obj)['sha256'] or
            receipt['inspector_build'] != policy['inspector_build'] or
            receipt['normalized_flags'] != recorded_flags or not path_matches):
        raise ValueError('The migrated object differs from its authenticated receipt.')
    # Relocate owned bindings only by their exact workspace-relative path.
    relocated = []
    for row in receipt['imported_objects']:
        selected = Path(row['object']['path']).resolve()
        if gate:
            selected = relocate(publication, row['module'], selected, workspace)
        elif selected.is_relative_to(old_workspace):
            selected = workspace / selected.relative_to(old_workspace)
        relocated.append({'module': row['module'], 'object':
                          {'path': str(selected), 'sha256': row['object']['sha256']}})
    ready = origin_context(policy, accepted)
    if receipt['coqdep'] not in ready['bindings']:
        raise ValueError('The migration resolver lacks its accepted runtime binding.')
    rows, result = comparisons(policy, module, obj, effective, receipt['coqdep'], recorded=relocated,
                               supplier=accepted['publication'])
    # Recompute every digest comparison. A forged successful subset never grants reuse.
    original = receipt['comparison']
    if (len(original.get('checks', [])) != len(rows) or
            {row['module'] for row in original['checks']} != {row['module'] for row in rows} or
            any(row.get('compatible') is not True for row in original['checks'])):
        raise ValueError('The migration receipt lacks complete successful comparisons.')
    return {row['module']: row['object'] for row in rows
            if Path(row['object']['path']).resolve().is_relative_to(workspace)}, workspace


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--origin', required=True, type=Path)
    parser.add_argument('--origin-sha256', required=True)
    parser.add_argument('--runtime', required=True, type=Path)
    parser.add_argument('--runtime-sha256', required=True)
    selection = parser.add_mutually_exclusive_group(required=True)
    selection.add_argument('--module', action='append')
    selection.add_argument('--all-owned', action='store_true')
    parser.add_argument('--output', required=True, type=Path)
    args = parser.parse_args()
    runtime = read_bound({'path': str(args.runtime), 'sha256': args.runtime_sha256})
    reference = {'path': str(args.origin), 'sha256': args.origin_sha256}
    policy = json.loads(POLICY.read_text())
    authority = next((row for row in policy['origins'] if row['binding'] == reference), None)
    if authority is None:
        raise ValueError('The migration origin is not an approved publication.')
    if authority['kind'] == 'accepted-correctness-gate-objects':
        from gate_object_origin import context
        config, publication, selected = context(authority, reference, bound_record)
        if {'path': str(args.runtime), 'sha256': args.runtime_sha256} != publication['resolution_runtime']:
            raise ValueError('The gate migration names another resolution runtime.')
        runtime = config
    if authority['kind'] == 'accepted-closed-compilations':
        from closed_compilation_origin import context
        config, publication, selected, _ = context(authority, reference, bound_record)
        runtime_reference = {'path': str(args.runtime), 'sha256': args.runtime_sha256}
        if runtime_reference == publication['inner_runtime']:
            runtime = config
    workspace = Path(runtime['prepared_workspace']).resolve()
    if args.all_owned:
        publication = read_bound(reference)
        names = ([row['module'] for row in publication['modules']] if
                 authority['kind'] == 'accepted-correctness-gate-objects' else
                 [row['module'] for row in publication['successful_modules']] if
                 authority['kind'] == 'accepted-closed-compilations' else
                 [row['module'] for row in publication['modules']] if
                 authority['kind'] == 'accepted-supplier' else list(runtime['proof_runtime']['module_files']))
        modules = [name for name in names if name in runtime['proof_runtime']['module_files'] and
                   (workspace / runtime['proof_runtime']['module_files'][name]).resolve().is_relative_to(workspace)]
    else:
        modules = args.module
    if len(set(modules)) != len(modules):
        raise ValueError('The migration request repeats a module.')
    compiler = next(row for row in runtime['bindings'] if Path(row['path']).name == 'coqc')
    args.output.mkdir(exist_ok=False)
    accepted, refused, costs = {}, [], []
    with batch() as counters:
        for module in modules:
            started, cpu = time.perf_counter(), time.process_time()
            children = resource.getrusage(resource.RUSAGE_CHILDREN)
            source = workspace / runtime['proof_runtime']['module_files'][module]
            try:
                receipt = create(reference, module, source, source.with_suffix('.vo'),
                                 compiler, runtime['physical_flags'], workspace)
                path = args.output / (module + '.json')
                path.write_text(json.dumps(receipt, indent=2) + '\n')
                accepted[module] = binding(path)
            except (ValueError, OSError, KeyError, TypeError) as error:
                refused.append({'module': module, 'reason': str(error)})
            after = resource.getrusage(resource.RUSAGE_CHILDREN)
            costs.append({'module': module, 'elapsed_seconds': time.perf_counter()-started,
                          'Python_process_CPU_seconds': time.process_time()-cpu,
                          'child_user_CPU_seconds': after.ru_utime-children.ru_utime,
                          'child_system_CPU_seconds': after.ru_stime-children.ru_stime})
            print(json.dumps({'module': module, 'migrated': module in accepted}), flush=True)
        statistics = {name: counters[name] for name in ['inspector_calls', 'inspector_hits']}
    manifest = args.output / 'MIGRATIONS.json'
    manifest.write_text(json.dumps({'schema': 'entry-chain.object-import-migrations.v1',
                                  'receipts': accepted}, indent=2) + '\n')
    result = {'schema': 'entry-chain.object-import-migration-batch.v1',
              'origin': reference, 'runtime': {'path': str(args.runtime), 'sha256': args.runtime_sha256},
              'manifest': binding(manifest), 'refused': refused, 'costs': costs,
              'cache_statistics': statistics, 'Rocq_compiler_calls': 0, 'proof_calls': 0,
              'CPU_qualification': 'Python process CPU excludes inspector and coqdep child CPU.'}
    (args.output / 'RESULT.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(binding(manifest)), flush=True)


if __name__ == '__main__':
    main()
