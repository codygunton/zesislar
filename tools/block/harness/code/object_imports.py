"""Reject owned object reuse without authenticated imported-object hashes."""
from pathlib import Path

from binding_cache import digest
from entry_chain import read_bound


def normalized_flags(flags, workspace):
    return [word.replace(str(workspace), '{workspace}') for word in flags]


def _record(reference, module, source, obj, compiler, flags, workspace):
    receipt = read_bound(reference)
    provenance = receipt.get('import_provenance')
    if not isinstance(provenance, dict) or provenance.get('schema') != 'entry-chain.object-imports.v1':
        raise ValueError('The owned object lacks authenticated import hashes.')
    old_workspace = provenance['owned_workspace']
    if (provenance.get('module') != module or receipt.get('successful_compilation') is not True or
            receipt.get('tool_result', {}).get('success') is not True or
            receipt.get('source', {}).get('sha256') != digest(source) or
            receipt.get('object', {}).get('sha256') != digest(obj) or
            provenance.get('compiler') != compiler or receipt.get('compiler') != compiler or
            provenance.get('normalized_flags') != normalized_flags(flags, workspace) or
            provenance['normalized_flags'] != normalized_flags(receipt['normalized_flags'], old_workspace)):
        raise ValueError('The owned object differs from its compilation provenance.')
    old_source = Path(receipt['source']['path'])
    if (not old_source.resolve().is_relative_to(Path(old_workspace).resolve()) or
            old_source.resolve().relative_to(Path(old_workspace).resolve()) != source.resolve().relative_to(workspace) or
            Path(receipt['object']['path']) != old_source.with_suffix('.vo')):
        raise ValueError('The owned object has another recorded source mapping.')
    physical = read_bound(receipt['physical_result'])
    inputs = read_bound(physical['input'])
    if (physical.get('returncode') != 0 or physical.get('output_validation', {}).get('success') is not True or
            physical.get('output_capture', {}).get('complete') is not True or
            physical.get('compiler_outputs', {}).get('object', {}).get('binding') != receipt['object'] or
            physical.get('input_validation') != provenance['validation'] or
            inputs.get('source') != receipt['source'] or inputs.get('compiler') != compiler or
            inputs.get('owned_workspace') != old_workspace or
            inputs.get('physical_argv') != [compiler['path'], *receipt['normalized_flags'], receipt['source']['path']] or
            physical.get('physical_argv') != inputs['physical_argv'] or
            inputs.get('validation', {}).get('snapshot') != receipt.get('snapshot')):
        raise ValueError('The owned object lacks its matching physical compiler record.')
    validation = read_bound(provenance['validation'])
    if validation.get('snapshot') != receipt.get('snapshot'):
        raise ValueError('The imported hashes name another compiler snapshot.')
    physical_hashes = {str(Path(row['path']).resolve()): row['sha256']
                       for row in validation['directly_hashed_inputs']}
    imports = {}
    for row in provenance['imported_objects']:
        name, selected = row['module'], row['object']
        if name in imports or physical_hashes.get(str(Path(selected['path']).resolve())) != selected['sha256']:
            raise ValueError('An imported object lacks one recorded physical hash.')
        imports[name] = selected
    return imports, Path(old_workspace)


def compatibility(targets, edges, modules, workspace, receipts, compiler, flags, *, planned=()):
    """Schedule unknown or changed owned imports through ordinary invalidation."""
    from entry_chain_stage import graph_closure
    workspace = Path(workspace).resolve()
    forward = {}
    for row in edges:
        forward.setdefault(row['from'], set()).add(row['to'])
    required = graph_closure(targets, forward)
    owned = {}
    for name in required:
        if name not in modules:
            continue
        source = workspace / modules[name]
        if source.resolve().is_relative_to(workspace):
            owned[name] = source
    planned = set(planned)
    checked, rebuild = [], []
    for name in sorted(owned):
        if name in planned:
            continue
        source = owned[name]
        obj = source.with_suffix('.vo')
        if not obj.is_file():
            continue  # The missing-object planner already schedules this source.
        try:
            if name not in receipts:
                raise ValueError('The owned object has no authenticated compilation receipt.')
            imports, old_workspace = _record(receipts[name], name, source, obj, compiler, flags, workspace)
            for dependency in sorted(graph_closure(forward.get(name, ()), forward)):
                if dependency not in owned:
                    continue  # Pinned installed libraries remain compiler inputs.
                if dependency in planned:
                    raise ValueError('An owned import has scheduled source compilation: ' + dependency)
                current = owned[dependency].with_suffix('.vo')
                recorded = imports.get(dependency)
                if recorded is None:
                    raise ValueError('An owned import lacks its recorded object hash: ' + dependency)
                old_object = Path(recorded['path'])
                if (not old_object.resolve().is_relative_to(old_workspace.resolve()) or
                        old_object.resolve().relative_to(old_workspace.resolve()) != current.resolve().relative_to(workspace) or
                        not current.is_file() or digest(current) != recorded['sha256']):
                    raise ValueError('An owned imported object differs: ' + dependency)
            checked.append(name)
        except (KeyError, TypeError, ValueError, OSError) as error:
            rebuild.append({'module': name, 'reason': str(error)})
    return {'schema': 'entry-chain.object-import-compatibility.v1',
            'compatible_owned_modules': checked, 'rebuild': rebuild,
            'rebuild_modules': [row['module'] for row in rebuild],
            'rule': 'Unknown provenance or changed imported objects require source compilation.'}
