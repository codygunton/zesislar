"""Reject owned object reuse without authenticated imported-object hashes."""
from pathlib import Path

from binding_cache import digest
from entry_chain import read_bound, binding
from source_context import compilation
from import_graph import graph_closure


def normalized_flags(flags, workspace):
    return [word.replace(str(workspace), '{workspace}') for word in flags]


def _record(reference, module, source, obj, compiler, flags, workspace):
    receipt = read_bound(reference)
    provenance = receipt.get('import_provenance')
    if not isinstance(provenance, dict) or provenance.get('schema') != 'entry-chain.object-imports.v1':
        raise ValueError('The owned object lacks authenticated import hashes.')
    old_workspace = provenance['owned_workspace']
    context=compilation(flags,binding(source))
    if (provenance.get('module') != module or receipt.get('successful_compilation') is not True or
            receipt.get('tool_result', {}).get('success') is not True or
            receipt.get('source', {}).get('sha256') != digest(source) or
            receipt.get('object', {}).get('sha256') != digest(obj) or
            provenance.get('compiler') != compiler or receipt.get('compiler') != compiler or
            provenance.get('normalized_flags') != normalized_flags(context['physical_flags'], workspace) or
            provenance['normalized_flags'] != normalized_flags(receipt['normalized_flags'], old_workspace)):
        raise ValueError('The owned object differs from its compilation provenance.')
    old_source = Path(receipt['source']['path'])
    if (not old_source.resolve().is_relative_to(Path(old_workspace).resolve()) or
            old_source.resolve().relative_to(Path(old_workspace).resolve()) != source.resolve().relative_to(workspace) or
            Path(receipt['object']['path']) != old_source.with_suffix('.vo')):
        raise ValueError('The owned object has another recorded source mapping.')
    physical = read_bound(receipt['physical_result'])
    inputs = read_bound(physical['input'])
    old_context=receipt.get('compiler_context')
    if context['changes'] or old_context is not None:
        recorded_context=inputs.get('compiler_context')
        # Legacy physical records omit the descriptor when their flags stay exact.
        unchanged_legacy=(recorded_context is None and not context['changes'] and
                          isinstance(old_context,dict) and old_context.get('changes')==[] and
                          old_context.get('base_flags')==old_context.get('physical_flags'))
        if (not isinstance(old_context,dict) or
                old_context.get('schema')!='entry-chain.source-context.v1' or
                recorded_context!=old_context and not unchanged_legacy or
                old_context.get('source')!=receipt['source'] or
                normalized_flags(old_context.get('base_flags',[]),old_workspace)!=normalized_flags(flags,workspace) or
                old_context.get('physical_flags')!=receipt['normalized_flags']):
            raise ValueError('The owned object has another compiler source context.')
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
    selection = validation.get('import_selection')
    if (not isinstance(selection, dict) or selection.get('module') != module or
            selection.get('owned_workspace') != old_workspace or
            selection.get('source') != receipt['source'] or
            selection.get('imported_objects') != provenance['imported_objects']):
        raise ValueError('The imported hashes differ from the recorded physical selection.')
    read_bound(selection['graph'])
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
            expected = graph_closure(forward.get(name, ()), forward) & owned.keys()
            extra = set(imports) - expected
            if extra:
                raise ValueError('A recorded owned import is absent from the current closure: ' + sorted(extra)[0])
            for dependency in sorted(expected):
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


def require_reuse(config, runtime, workspace):
    """Refuse a staged plan that would retain an incompatible owned object."""
    graph = read_bound(config['cache_import_graph'])
    modules = runtime['module_files']
    planned = list(runtime['ordered_modules'])
    targets = planned + [row['target']['module'] for row in config['jobs']
                         if (row.get('target') or {}).get('module')]
    native_outputs = {row['target']['module'] for row in config['jobs']
                      if row.get('phase') == 'native' and (row.get('target') or {}).get('module')}
    native = runtime.get('target', {}).get('block') or {}
    if native.get('module'):
        native_outputs.add(native['module'])
    forward = {}
    for row in graph['import_edges']:
        forward.setdefault(row['from'], set()).add(row['to'])
    imported = set()
    for name in targets:
        imported.update(graph_closure(forward.get(name, ()), forward))
    # A future native output is not reused unless another required module imports it.
    planned.extend(native_outputs - imported)
    result = compatibility(targets, graph['import_edges'], modules, workspace,
                           config.get('object_imports', {}), runtime['physical_compiler'],
                           runtime['physical_flags'], planned=planned)
    if result['rebuild']:
        first = result['rebuild'][0]
        raise ValueError('The staged plan must rebuild an owned object: ' +
                         first['module'] + ': ' + first['reason'])
    return result
