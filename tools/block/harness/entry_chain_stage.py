"""Stage compatible imports and invalidate the changed chain dependency closure."""
from pathlib import Path
import shutil

from check_entry import affected_order
from check_data_only_lemmas import command_imports, rocq_commands
from entry_chain import binding, check_bindings, digest, relative, save
from entry_pilot import copy_bound
from installed_mappings import require_imports


def graph_closure(seeds, graph):
    found, pending = set(seeds), list(seeds)
    while pending:
        for name in graph.get(pending.pop(), ()):
            if name not in found:
                found.add(name)
                pending.append(name)
    return found


def import_commands(source):
    """Retain complete import commands, including From, Import, and Export."""
    result = []
    for command in rocq_commands(source):
        words = [word for word, _ in command]
        requests = require_imports(words)
        if requests is None:
            names, _ = command_imports(words)
        else:
            names = [request['module'] for request in requests]
        if names:
            result.append((words, names))
    return result


def import_edges(seed_edges, changed_sources, module_files, original_sources, resolver=None):
    """Use compiled canonical identities only after exact header comparison."""
    result = list(seed_edges)
    known = {(row['from'], row['to']) for row in result}
    additions = []
    for module, source in changed_sources.items():
        commands = import_commands(source)
        if module not in original_sources:
            raise ValueError('A changed module lacks its exact original source: '+module)
        if commands == import_commands(original_sources[module]):
            # The entire sequence is exact. The bound seed supplies canonical edges.
            continue
        current_edges = []
        for _, names in commands:
            for name in names:
                if (module, name) in known:
                    # This exact canonical identity remains valid for the unchanged mapping.
                    canonical = name
                elif name in module_files:
                    canonical = name
                else:
                    matches = list(resolver(module, name)) if resolver is not None else []
                    if len(matches) != 1:
                        raise ValueError('A changed header has an unresolved or ambiguous import: '+name)
                    canonical = matches[0]
                    if canonical not in module_files:
                        raise ValueError('A resolved import lacks its source/object mapping: '+canonical)
                row = {'from': module, 'to': canonical}
                if row not in current_edges:
                    current_edges.append(row)
                if (module, canonical) not in known:
                    additions.append(row)
                    known.add((module, canonical))
        # A changed header replaces its old direct edge set. Removed imports are not ancestors.
        result = [row for row in result if row['from'] != module] + current_edges
    return result, additions


def invalidation(edges, changed, targets):
    reverse = {}
    for edge in edges:
        reverse.setdefault(edge['to'], set()).add(edge['from'])
    invalid = graph_closure(changed, reverse)
    ordered = affected_order(edges, changed, targets)
    native = set(targets)
    return {'changed_modules': sorted(set(changed)), 'invalidated_modules': sorted(invalid),
            'ordered_required': ordered,
            'prerequisites': [name for name in ordered if name not in native],
            'native_targets': [name for name in ordered if name in native],
            'unused_invalidated': sorted(invalid-set(ordered)),
            'rule': 'Invalidate all changed dependents. Compile only required ancestors of native targets.'}


def stage_seed(seed, workspace, report):
    workspace = Path(workspace).resolve()
    workspace.mkdir(parents=True, exist_ok=False)
    copies = []
    for row in seed['copies']:
        target = workspace/relative(row['relative_path'])
        item = copy_bound(row['source'], target, row['sha256'])
        source_info, target_info = Path(row['source']).stat(), target.stat()
        if (source_info.st_dev, source_info.st_ino) == (target_info.st_dev, target_info.st_ino):
            raise ValueError('A seed object shares its original inode.')
        target.chmod(row['mode'])
        copies.append({**item, 'relative_path': row['relative_path'], 'distinct_inode': True})
    for directory in seed.get('empty_dirs', []):
        (workspace/relative(directory)).mkdir(parents=True, exist_ok=True)
    for row in seed['relocations']:
        path = workspace/relative(row['relative_path'])
        if digest(path) != row['source_sha256']:
            raise ValueError('A project relocation input changed.')
        text = path.read_text()
        for old, new in row['replacements']:
            text = text.replace(old, str(workspace)+new)
        path.write_text(text)
    for row in seed['source_links']:
        link = workspace/relative(row['relative_path'])
        resolved = (link.parent/row['target']).resolve()
        if not resolved.is_relative_to(workspace) or not resolved.exists():
            raise ValueError('A seed alias leaves its owned workspace.')
        link.parent.mkdir(parents=True, exist_ok=True)
        link.symlink_to(row['target'], target_is_directory=resolved.is_dir())
    save(report, {'copies': copies, 'source_compilation': False, 'object_reuse': 'Retain only compatible objects outside the complete invalidated closure.'})
    return copies


def install_source_overrides(rows, module_files, replacements, install):
    seen=set()
    for row in rows:
        if set(row)!={'module','source','required_by_pcs'}:
            raise ValueError('A source override has unexpected fields.')
        module=row['module']
        if module!='ZesuSsz.Compliance.DecodeItemHints' or module not in module_files or module in seen:
            raise ValueError('A source override has an unsupported, absent, or repeated module.')
        pcs=row['required_by_pcs']
        if not isinstance(pcs,list) or not pcs or len(set(pcs))!=len(pcs) or not set(pcs)<=set(replacements):
            raise ValueError('A source override has invalid required PCs.')
        if not Path(row['source']['path']).is_absolute():
            raise ValueError('A source override requires an absolute bound path.')
        seen.add(module)
        install(module,row['source'])


def install_private(seed, workspace, prepared, native, replacements, report_dir, *, source_overrides=()):
    workspace, report_dir = Path(workspace), Path(report_dir)
    module_files = seed['module_files']
    changed = []
    source_changes = []
    original_sources = {module: (workspace/relative(name)).read_text()
                        for module, name in module_files.items()}
    def install(module, source):
        if digest(source['path']) != source['sha256']:
            raise ValueError('A prepared chain source changed.')
        text = Path(source['path']).read_text()
        physical = workspace/relative(module_files[module])
        logical = workspace/Path(*module.split('.')).with_suffix('.v')
        old = digest(physical)
        if physical.read_text() != text:
            changed.append(module)
        physical.write_text(text)
        if logical != physical and logical.exists():
            logical.write_text(text)
        source_changes.append({'module': module, 'original_sha256': old, 'private_source': binding(physical)})
    for row in prepared['outputs']:
        name = Path(row['path'])
        # The three generated modules have explicit canonical names.
        stem = name.stem
        if stem not in ('Entries', 'Registrations', 'BootstrapRegistrations'):
            raise ValueError('The preparation includes another generated module.')
        install('ZesuSsz.Generated.DecodeItem.'+stem, row)
    for row in native['rows']:
        install(row['module'], row['private_source'])
    install_source_overrides(source_overrides, module_files, replacements, install)
    # The old helper filter remains exact. Preserve one exclusion receipt per entry.
    from h0_route import prepare_helpers
    helper_changes = []
    for pc in replacements:
        target_output = report_dir/'helper-stages'/pc
        target_output.mkdir(parents=True, exist_ok=False)
        helper_changes.extend(prepare_helpers(seed, workspace, pc, target_output))
    changed.extend(helper_changes)
    changed_sources = {module: (workspace/relative(module_files[module])).read_text()
                       for module in set(changed)}
    edges, additions = import_edges(seed['import_edges'], changed_sources, module_files, original_sources)
    targets = [row['module'] for row in native['rows']]
    plan = invalidation(edges, changed, targets)
    plan.update(new_import_edges=additions,
                removed_import_edges=[row for row in seed['import_edges'] if row not in edges],
                source_changes=source_changes,
                helper_exclusion_stages=[str(report_dir/'helper-stages'/pc/'H0-EXCLUDED-OBLIGATIONS.json')
                                         for pc in replacements])
    removed = []
    for module in plan['invalidated_modules']:
        if module not in module_files:
            raise ValueError('An invalidated module lacks its physical mapping: '+module)
        physical = workspace/relative(module_files[module])
        logical = workspace/Path(*module.split('.')).with_suffix('.v')
        for path in {physical, logical}:
            for suffix in ('.vo', '.vos', '.vok', '.glob'):
                target = path.with_suffix(suffix)
                if target.exists():
                    removed.append(binding(target))
                    target.unlink()
            (path.parent/('.'+path.stem+'.aux')).unlink(missing_ok=True)
    plan['removed_objects'] = removed
    plan['import_edges'] = edges
    plan['proof_ran'] = False
    plan['compiler_ran'] = False
    save(report_dir/'INVALIDATION.json', plan)
    return plan
