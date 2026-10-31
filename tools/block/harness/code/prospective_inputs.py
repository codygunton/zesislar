"""Build fresh typed inputs from the actual private source and object closure."""
import hashlib
from pathlib import Path

from installed_mappings import InstalledMappings


def digest(path):
    value = hashlib.sha256()
    with Path(path).open('rb') as stream:
        for data in iter(lambda: stream.read(1024 * 1024), b''):
            value.update(data)
    return value.hexdigest()


def physical_mappings(flags):
    return [(flags[index], Path(flags[index + 1]), flags[index + 2])
            for index in range(len(flags)) if flags[index] in {'-Q', '-R'}]


def imported_closure(module, graph):
    edges = {}
    for row in graph['import_edges']:
        edges.setdefault(row['from'], []).append(row['to'])
    pending, seen = [module], set()
    while pending:
        name = pending.pop()
        if name in seen:
            continue
        seen.add(name)
        pending.extend(edges.get(name, []))
    return sorted(seen), edges


def module_source(module, runtime, workspace, installed=None):
    if module in runtime['module_files']:
        path = workspace / runtime['module_files'][module]
        if not path.is_file():
            raise ValueError('A declared module source is absent: ' + module)
        target = runtime.get('target', {}).get('block', {}).get('module')
        if module != target:
            installed = installed if installed is not None else InstalledMappings(runtime['physical_flags'])
            if installed.resolve(module).resolve() != path.resolve():
                raise ValueError('The compiler-resolved private import differs from its declared source: ' + module)
        return path
    installed = installed if installed is not None else InstalledMappings(runtime['physical_flags'])
    return installed.resolve(module)


def build(*, block, runtime, workspace, graph, roots, configuration,
          attempt, backend_files, producer_files, toolchain_files, installed=None):
    """Hash only current inputs. Missing prerequisite objects cause refusal.

    configuration supplies the explicit environment and every ordered vector.
    The collector expands installed runtime and package inventories afterward.
    No historical runtime identity is assigned to a current artifact.
    """
    workspace = Path(workspace).resolve()
    root_map = {row['role']: Path(row['path']).resolve() for row in roots}
    target = runtime['target']['block']
    module = target['module']
    seen, edges = imported_closure(module, graph)
    files, nodes, by_module = {}, {}, {}
    installed = installed if installed is not None else InstalledMappings(runtime['physical_flags'])

    def add(name, path, kind, expected=None):
        path = Path(path).absolute()
        actual = digest(path)
        if expected is not None and actual != expected:
            raise ValueError('A prospective source input changed: ' + name)
        candidates = [(len(root.parts), role) for role, root in root_map.items()
                      if path.resolve().is_relative_to(root)]
        if not candidates:
            raise ValueError('A prospective file has no declared root: ' + name)
        row = {'id': name, 'path': str(path), 'kind': kind, 'sha256': actual,
               'root_role': max(candidates)[1]}
        if path.is_symlink():
            row['symlink_target'] = path.readlink().as_posix()
        if name in files and files[name] != row:
            raise ValueError('A prospective input repeats a different file identity.')
        files[name] = row
        nodes.setdefault(name, {'id': name, 'requires': []})
        return name

    for name in seen:
        source = module_source(name, runtime, workspace, installed)
        ids = []
        if source.is_file():
            ids.append(add('module:' + name + ':source', source,
                           'generated_source' if name == module else 'source',
                           target['source_sha256'] if name == module else None))
        if name != module:
            obj = source.with_suffix('.vo')
            if not obj.is_file():
                raise ValueError('A current prerequisite object is absent: ' + name)
            ids.append(add('module:' + name + ':object', obj, 'object'))
        by_module[name] = ids
    proof = 'module:' + module + ':source'
    if proof not in files:
        raise ValueError('The current native proof source is absent.')
    for name in seen:
        required = [file_id for dependency in edges.get(name, []) for file_id in by_module[dependency]]
        for file_id in by_module[name]:
            nodes[file_id]['requires'] = list(dict.fromkeys(required))

    def declared(row):
        return add(row['id'], row['path'], row['kind'], row['sha256'])

    backend_ids = [declared(row) for row in backend_files]
    producer_ids = {group: [declared(row) for row in rows] for group, rows in producer_files.items()}
    if set(producer_ids) != {'implementation', 'inputs', 'outputs'}:
        raise ValueError('The source producer declaration is incomplete.')
    roles = ['compiler', 'ocaml_runtime', 'standard_library', 'pet', 'coq_lsp', 'mcp',
             'python', 'python_dependencies', 'plugins', 'solvers', 'dynamic_libraries']
    if set(toolchain_files) != set(roles):
        raise ValueError('The toolchain role inventory is incomplete.')
    toolchain = {role: [declared(row) for row in toolchain_files[role]] for role in roles}
    nodes[proof]['requires'] = list(dict.fromkeys(nodes[proof]['requires'] + backend_ids +
                                [file_id for rows in producer_ids.values() for file_id in rows] +
                                [file_id for rows in toolchain.values() for file_id in rows]))
    from native_route import validate_closure,runtime_body
    validate_closure(runtime,seen,list(files.values()))
    return {'schema': 'zesu-proof-key-input-v2', 'block': block, 'roots': roots,
            'files': list(files.values()),
            'recipe': {'schema': 'zesu-proof-recipe-v1', 'module': module, 'proof': proof,
                       'dependencies': list(nodes.values()),
                       'producers': [{'id': 'forward-V2-source', **producer_ids}],
                       'imports': seen, 'toolchain': toolchain, 'configuration': configuration,
                       'backend': {'files': backend_ids, 'tactics': [runtime_body(runtime)],
                                   'features': {'phase': 'native', 'custom_observer': False, 'control_sessions_disabled': True, 'dependency_waves_disabled': True,
                                                'source_mode': 'forward-stage1', 'e1': False, 'V3': False, 'complete_export_PET_seconds':30}},
                       'acceptance': {'method': 'module_m', 'compilation': 'vo', 'allowed_assumptions': []}},
            'attempt': attempt}
