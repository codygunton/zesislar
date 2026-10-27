"""Typed proof identities from CACHE-KEY-SPEC.md.

Files, dependency nodes, producer nodes, and scope rows are named sets.
Arithmetic caches use their fixed schema order. All other arrays preserve
order. Source bytes remain exact. Physical locations occur only in the
checked input envelope.
"""
from copy import deepcopy
import hashlib
import json
import math
from pathlib import Path, PurePosixPath
import re


INPUT_SCHEMA = 'zesu-proof-key-input-v2'
RECIPE_SCHEMA = 'zesu-proof-recipe-v1'
ATTEMPT_SCHEMA = 'zesu-proof-attempt-v1'
ARTIFACT_SCHEMA = 'zesu-proof-artifact-v1'


def json_value(value):
    if isinstance(value, dict):
        if any(not isinstance(key, str) for key in value):
            raise ValueError('A JSON object has a non-string key.')
        for child in value.values():
            json_value(child)
    elif isinstance(value, list):
        for child in value:
            json_value(child)
    elif type(value) is float:
        if not math.isfinite(value):
            raise ValueError('A JSON value contains a non-finite number.')
    elif type(value) not in {str, int, bool, type(None)}:
        raise ValueError('A JSON value has an unsupported type.')


def canonical(value):
    json_value(value)
    return json.dumps(value, sort_keys=True, ensure_ascii=False,
                      separators=(',', ':'), allow_nan=False).encode('utf-8')


def identity(domain, value):
    return hashlib.sha256(domain.encode('ascii') + b'\0' + canonical(value)).hexdigest()


def strict_loads(text):
    def pairs(rows):
        value = {}
        for key, item in rows:
            if key in value:
                raise ValueError('The key input contains a duplicate JSON key.')
            value[key] = item
        return value
    def constant(_):
        raise ValueError('The key input contains a non-finite number.')
    value = json.loads(text, object_pairs_hook=pairs, parse_constant=constant)
    json_value(value)
    return value


def fields(value, required, optional=()):
    if not isinstance(value, dict) or set(value) - set(required) - set(optional) or set(required) - set(value):
        raise ValueError('A typed key record has missing or unknown fields.')


def string(value):
    if not isinstance(value, str) or not value or '\0' in value:
        raise ValueError('A key string is empty or has an invalid type.')
    return value


def strings(value):
    if not isinstance(value, list):
        raise ValueError('An ordered string array has an invalid type.')
    return [string(item) for item in value]


def sha256(value):
    if not isinstance(value, str) or not re.fullmatch('[0-9a-f]{64}', value):
        raise ValueError('A content identity is not a SHA256 digest.')
    return value


def relative(value):
    if not isinstance(value, str) or not value or PurePosixPath(value).is_absolute() or '..' in PurePosixPath(value).parts:
        raise ValueError('A declared relative path leaves its root.')
    return value


def file_digest(path):
    value = hashlib.sha256()
    with path.open('rb') as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b''):
            value.update(chunk)
    return value.hexdigest()


def roots_by_role(rows):
    if not isinstance(rows, list) or not rows:
        raise ValueError('The key input has no declared roots.')
    roots = {}
    for row in rows:
        fields(row, {'role', 'path'})
        role = string(row['role'])
        path = Path(string(row['path']))
        if not path.is_absolute() or not path.is_dir():
            raise ValueError('A declared root is not an absolute directory.')
        path = path.resolve()
        if role in roots or path in roots.values():
            raise ValueError('A root mapping is ambiguous.')
        roots[role] = path
    return roots


def path_value(value, roots):
    fields(value, {'kind', 'value', 'root_role'})
    if value['kind'] != 'path':
        raise ValueError('A path argument has another value kind.')
    role = string(value['root_role'])
    if role not in roots:
        raise ValueError('A path argument has an unresolved root role.')
    path = Path(string(value['value']))
    if not path.is_absolute():
        raise ValueError('A physical path argument is not absolute.')
    path = path.resolve()
    if not path.is_relative_to(roots[role]):
        raise ValueError('A path argument escapes its declared boundary.')
    return {'kind': 'path', 'root_role': role,
            'relative_path': path.relative_to(roots[role]).as_posix()}


def typed_value(value, roots, *, path_lists=True):
    if not isinstance(value, dict):
        raise ValueError('An execution value is not typed.')
    if value.get('kind') == 'path':
        return path_value(value, roots)
    if value.get('kind') == 'transport':
        fields(value, {'kind', 'role', 'encoding', 'binding', 'semantic_projection', 'semantic_dependencies'},
               {'selector'} if value.get('encoding') == 'json-field' else ())
        string(value['role'])
        string(value['semantic_projection'])
        strings(value['semantic_dependencies'])
        if not value['semantic_dependencies']:
            raise ValueError('A transport reference has no semantic dependency projection.')
        if value['encoding'] not in {'json-path', 'sha256', 'json-field'}:
            raise ValueError('A transport reference has an unsupported encoding.')
        binding = value['binding']
        fields(binding, {'path', 'sha256', 'root_role'})
        path_value({'kind': 'path', 'value': binding['path'], 'root_role': binding['root_role']}, roots)
        path = Path(binding['path'])
        if path.is_symlink() or file_digest(path) != sha256(binding['sha256']):
            raise ValueError('The separately bound transport envelope changed.')
        result = {name: value[name] for name in ('kind', 'role', 'encoding',
                                                 'semantic_projection', 'semantic_dependencies')}
        if value['encoding'] == 'json-field':
            selector = strings(value.get('selector'))
            if not selector:
                raise ValueError('A transport field selector is empty.')
            selected = strict_loads(path.read_text())
            for name in selector:
                if not isinstance(selected, dict) or name not in selected:
                    raise ValueError('A transport field selector does not resolve.')
                selected = selected[name]
            string(selected)
            result['selector'] = selector
        return result
    if value.get('kind') == 'literal':
        fields(value, {'kind', 'value'})
        if not isinstance(value['value'], str) or '\0' in value['value']:
            raise ValueError('A literal execution value is not a string.')
        return dict(value)
    if path_lists and value.get('kind') == 'paths':
        fields(value, {'kind', 'values'})
        if not isinstance(value['values'], list):
            raise ValueError('A path list has an invalid type.')
        return {'kind': 'paths', 'values': [path_value(row, roots) for row in value['values']]}
    raise ValueError('An execution value has an unsupported kind.')


def checked_files(rows, roots):
    if not isinstance(rows, list) or not rows:
        raise ValueError('The dependency closure has no bound files.')
    result = {}
    for row in rows:
        fields(row, {'id', 'kind', 'path', 'sha256', 'root_role'}, {'symlink_target'})
        name, kind = string(row['id']), string(row['kind'])
        if name in result:
            raise ValueError('The dependency closure repeats a file identity.')
        path_value({'kind': 'path', 'value': row['path'], 'root_role': row['root_role']}, roots)
        path = Path(row['path'])
        if path.is_symlink():
            if 'symlink_target' not in row or path.readlink().as_posix() != row['symlink_target']:
                raise ValueError('A source symlink has no exact declared target.')
        elif 'symlink_target' in row:
            raise ValueError('A declared source symlink is absent.')
        expected = sha256(row['sha256'])
        if file_digest(path) != expected:
            raise ValueError('A bound dependency changed.')
        result[name] = {'id': name, 'kind': kind, 'sha256': expected}
    return result


def references(values, files):
    answer = strings(values)
    if any(name not in files for name in answer):
        raise ValueError('The recipe has an unresolved dependency.')
    return answer


def configuration(value, roots):
    names = {'argv', 'execution_vectors', 'load_paths', 'cwd', 'environment', 'init_file_policy',
             'warnings_as_errors', 'native_compilation', 'proof_skipping',
             'locale', 'python_version', 'python_hash_seed', 'solver_seeds'}
    fields(value, names)
    if not isinstance(value['argv'], list) or not isinstance(value['load_paths'], list):
        raise ValueError('Compiler argument arrays have invalid types.')
    argv = [typed_value(row, roots, path_lists=False) for row in value['argv']]
    inferred_paths = []
    for index, row in enumerate(argv):
        if row['kind'] == 'literal' and row['value'] in {'-Q', '-R', '-I', '-coqlib', '-o', '-native-output-dir', '-load-ml-object'}:
            if index + 1 == len(argv) or argv[index + 1]['kind'] != 'path':
                raise ValueError('A declared compiler path position is not typed.')
            if row['value'] in {'-Q', '-R', '-I', '-coqlib'}:
                logical = ''
                if row['value'] in {'-Q', '-R'}:
                    if index + 2 >= len(argv) or argv[index + 2]['kind'] != 'literal':
                        raise ValueError('A compiler mapping has no logical prefix.')
                    logical = argv[index + 2]['value']
                inferred_paths.append({'flag': row['value'],
                                       'physical_root_role': argv[index + 1]['root_role'],
                                       'relative_path': argv[index + 1]['relative_path'],
                                       'logical_prefix': logical, 'ordinal': len(inferred_paths)})
    load_paths = []
    for ordinal, row in enumerate(value['load_paths']):
        fields(row, {'flag', 'physical_root_role', 'relative_path', 'logical_prefix', 'ordinal'})
        if row['flag'] not in {'-Q', '-R', '-I', '-coqlib'} or type(row['ordinal']) is not int or row['ordinal'] != ordinal:
            raise ValueError('A load-path binding changed its order or flag.')
        if row['physical_root_role'] not in roots:
            raise ValueError('A load-path root role is unresolved.')
        relative(row['relative_path'])
        if not isinstance(row['logical_prefix'], str):
            raise ValueError('A logical prefix has an invalid type.')
        load_paths.append(dict(row))
    if load_paths != inferred_paths:
        raise ValueError('The load-path manifest differs from the ordered compiler arguments.')
    if not isinstance(value['environment'], dict):
        raise ValueError('The effective environment has an invalid type.')
    environment = {string(name): typed_value(item, roots) for name, item in value['environment'].items()}
    required = {'COQPATH', 'OCAMLPATH', 'CAML_LD_LIBRARY_PATH', 'PATH'}
    if not required.issubset(environment):
        raise ValueError('The effective environment omits a required path policy.')
    if any(environment[name]['kind'] != 'paths' for name in required):
        raise ValueError('An effective search path is not an ordered path list.')
    for name in ('init_file_policy', 'native_compilation', 'locale', 'python_version', 'python_hash_seed'):
        string(value[name])
    strings(value['warnings_as_errors'])
    if type(value['proof_skipping']) is not bool:
        raise ValueError('The proof-skipping policy has an invalid type.')
    if not isinstance(value['solver_seeds'], dict) or any(type(v) not in {str, int} for v in value['solver_seeds'].values()):
        raise ValueError('The solver seed policy has an invalid type.')
    result = {name: value[name] for name in names - {'argv', 'load_paths', 'cwd', 'environment'}}
    result.update(argv=argv, load_paths=load_paths, cwd=path_value(value['cwd'], roots), environment=environment)
    if not isinstance(value['execution_vectors'], list) or not value['execution_vectors']:
        raise ValueError('The recipe has no ordered execution vectors.')
    vectors = []
    roles = set()
    for row in value['execution_vectors']:
        fields(row, {'role', 'argv', 'cwd'})
        role = string(row['role'])
        if role in roles or not isinstance(row['argv'], list) or not row['argv']:
            raise ValueError('An execution vector is empty or repeats a role.')
        roles.add(role)
        vectors.append({'role': role,
                        'argv': [typed_value(item, roots, path_lists=False) for item in row['argv']],
                        'cwd': path_value(row['cwd'], roots)})
    result['execution_vectors'] = vectors
    return result


def acceptance(value):
    fields(value, {'method', 'compilation', 'allowed_assumptions'})
    if value != {'method': 'module_m', 'compilation': 'vo', 'allowed_assumptions': []}:
        raise ValueError('This cache requires full compilation and exact module_m verification.')
    return dict(value)


def recipe(value, files, roots):
    fields(value, {'schema', 'module', 'proof', 'dependencies', 'producers',
                   'imports', 'toolchain', 'configuration', 'backend', 'acceptance'})
    if value['schema'] != RECIPE_SCHEMA:
        raise ValueError('The recipe schema is unsupported.')
    string(value['module'])
    references([value['proof']], files)
    if files[value['proof']]['kind'] not in {'source', 'generated_source'}:
        raise ValueError('The proof identity does not bind theorem source bytes.')
    nodes = {}
    if not isinstance(value['dependencies'], list):
        raise ValueError('The dependency graph has an invalid type.')
    for node in value['dependencies']:
        fields(node, {'id', 'requires'})
        name = string(node['id'])
        if name in nodes or name not in files:
            raise ValueError('The dependency graph repeats or invents a node.')
        nodes[name] = references(node['requires'], files)
    if set(nodes) != set(files):
        raise ValueError('The dependency graph omits a bound file.')
    producers = {}
    if not isinstance(value['producers'], list):
        raise ValueError('The producer list has an invalid type.')
    for producer in value['producers']:
        fields(producer, {'id', 'implementation', 'inputs', 'outputs'})
        name = string(producer['id'])
        if name in producers:
            raise ValueError('The recipe repeats a producer identity.')
        producers[name] = {'id': name, **{field: references(producer[field], files)
                                        for field in ('implementation', 'inputs', 'outputs')}}
    fields(value['backend'], {'files', 'tactics', 'features'})
    backend = value['backend']
    references(backend['files'], files)
    strings(backend['tactics'])
    if not backend['files'] or not backend['tactics'] or not isinstance(backend['features'], dict):
        raise ValueError('The backend identity is incomplete.')
    if any(type(v) not in {str, int, bool, type(None)} for v in backend['features'].values()):
        raise ValueError('A backend feature has an invalid type.')
    toolchain_roles = {'compiler', 'ocaml_runtime', 'standard_library', 'pet',
                       'coq_lsp', 'mcp', 'python', 'python_dependencies',
                       'plugins', 'solvers', 'dynamic_libraries'}
    fields(value['toolchain'], toolchain_roles)
    toolchain = {role: references(value['toolchain'][role], files) for role in toolchain_roles}
    for role in toolchain_roles - {'plugins', 'solvers'}:
        if not toolchain[role]:
            raise ValueError('The installed toolchain closure is incomplete.')
    for role in ('compiler', 'pet', 'python'):
        if not any(files[name]['kind'] == 'binary' for name in toolchain[role]):
            raise ValueError('A toolchain role has no installed binary digest.')
    config = configuration(value['configuration'], roots)
    def check_transports(item):
        if isinstance(item, dict):
            if item.get('kind') == 'transport':
                references([item['semantic_projection'], *item['semantic_dependencies']], files)
            for child in item.values():
                check_transports(child)
        elif isinstance(item, list):
            for child in item:
                check_transports(child)
    check_transports(config)
    if config['proof_skipping'] or any(row.get('value') in {'-vos', '-vok', '-vio', '-quick'} for row in config['argv']):
        raise ValueError('Skipped proof bodies cannot enter this proof cache.')
    return {'schema': RECIPE_SCHEMA, 'module': value['module'], 'proof': value['proof'],
            'files': [files[name] for name in sorted(files)],
            'dependencies': [{'id': name, 'requires': nodes[name]} for name in sorted(nodes)],
            'producers': [producers[name] for name in sorted(producers)],
            'imports': strings(value['imports']), 'toolchain': toolchain,
            'configuration': config, 'backend': backend, 'acceptance': acceptance(value['acceptance'])}


def attempt(value, recipe_key, block, approved_acceptance, files, proof_source_sha256):
    fields(value, {'schema', 'limits', 'scope_limits', 'tool_timeouts', 'arithmetic_caches'})
    if value['schema'] != ATTEMPT_SCHEMA:
        raise ValueError('The attempt schema is unsupported.')
    limits = value['limits']
    fields(limits, {'cpu_seconds', 'wall_seconds', 'memory_bytes', 'swap_bytes', 'steps'})
    for number in limits.values():
        if number is not None and (type(number) is not int or number < 0):
            raise ValueError('An attempt limit has an invalid type.')
    if not isinstance(value['scope_limits'], list) or not value['scope_limits']:
        raise ValueError('The attempt has no physical scope hierarchy.')
    scopes = {}
    for scope in value['scope_limits']:
        fields(scope, {'role', 'parent', 'memory_bytes', 'swap_bytes', 'cpu_seconds', 'wall_seconds'})
        role = string(scope['role'])
        if role in scopes:
            raise ValueError('The scope hierarchy repeats a role.')
        for name in ('memory_bytes', 'swap_bytes', 'cpu_seconds', 'wall_seconds'):
            number = scope[name]
            if number is not None and (type(number) is not int or number < 0):
                raise ValueError('A scope limit has an invalid type.')
        scopes[role] = dict(scope)
    if any(row['parent'] is not None and row['parent'] not in scopes for row in scopes.values()):
        raise ValueError('The scope hierarchy has an unresolved parent.')
    for role in scopes:
        seen = set()
        while role is not None:
            if role in seen:
                raise ValueError('The scope hierarchy contains a cycle.')
            seen.add(role)
            role = scopes[role]['parent']
    fields(value['tool_timeouts'], {'rocq_call_seconds', 'pet_seconds', 'query_seconds'})
    for number in value['tool_timeouts'].values():
        if number is not None and (type(number) is not int or number < 0):
            raise ValueError('A tool timeout has an invalid type.')
    names = ['.lia.cache', '.nia.cache', '.nra.cache', '.csdp.cache']
    if not isinstance(value['arithmetic_caches'], list):
        raise ValueError('The arithmetic-cache policy has an invalid type.')
    caches = {}
    for row in value['arithmetic_caches']:
        fields(row, {'name', 'policy', 'initial_files', 'compiler_format'})
        if row['name'] not in names or row['name'] in caches:
            raise ValueError('An arithmetic cache is unsupported or repeated.')
        if row['policy'] not in {'empty-private', 'warm-private'}:
            raise ValueError('Writable shared arithmetic caches are forbidden.')
        references(row['initial_files'], files)
        string(row['compiler_format'])
        if (row['policy'] == 'empty-private') != (not row['initial_files']):
            raise ValueError('The arithmetic-cache policy differs from its initial contents.')
        caches[row['name']] = dict(row)
    if set(caches) != set(names):
        raise ValueError('The attempt omits an arithmetic cache policy.')
    return {'schema': ATTEMPT_SCHEMA, 'key_function': ATTEMPT_SCHEMA, 'block': string(block),
            'recipe_key': recipe_key, 'proof_source_sha256': proof_source_sha256,
            'acceptance': approved_acceptance,
            'limits': dict(limits), 'scope_limits': [scopes[name] for name in sorted(scopes)],
            'tool_timeouts': dict(value['tool_timeouts']),
            'arithmetic_caches': [caches[name] for name in names]}


def without_python_bytecode(spec):
    """Keep source and interpreter inputs. Omit their derived bytecode files."""
    spec = deepcopy(spec)
    if not isinstance(spec['files'], list):
        raise ValueError('The dependency closure has an invalid file list.')
    names = set()
    for row in spec['files']:
        fields(row, {'id', 'kind', 'path', 'sha256', 'root_role'}, {'symlink_target'})
        name = string(row['id'])
        if name in names:
            raise ValueError('The dependency closure repeats a file identity.')
        names.add(name)
        string(row['path'])
        string(row['kind'])
        string(row['root_role'])
        sha256(row['sha256'])
    excluded = {row['id'] for row in spec['files']
                if '__pycache__' in PurePosixPath(row['path']).parts
                or PurePosixPath(row['path']).suffix == '.pyc'}
    if not excluded:
        return spec
    if spec['recipe']['proof'] in excluded:
        raise ValueError('The proof source cannot be a Python bytecode file.')
    spec['files'] = [row for row in spec['files'] if row['id'] not in excluded]
    recipe = spec['recipe']
    for row in recipe['dependencies']:
        fields(row, {'id', 'requires'})
    recipe['dependencies'] = [dict(row, requires=[name for name in row['requires'] if name not in excluded])
                              for row in recipe['dependencies'] if row['id'] not in excluded]
    for row in recipe['producers']:
        fields(row, {'id', 'implementation', 'inputs', 'outputs'})
        for field in ['implementation', 'inputs', 'outputs']:
            row[field] = [name for name in row[field] if name not in excluded]
    for role, names in recipe['toolchain'].items():
        recipe['toolchain'][role] = [name for name in names if name not in excluded]
    recipe['backend']['files'] = [name for name in recipe['backend']['files'] if name not in excluded]
    return spec


def build_keys(spec):
    fields(spec, {'schema', 'block', 'roots', 'files', 'recipe', 'attempt'})
    if spec['schema'] != INPUT_SCHEMA:
        raise ValueError('The proof-key input schema is unsupported.')
    spec = without_python_bytecode(spec)
    roots = roots_by_role(spec['roots'])
    files = checked_files(spec['files'], roots)
    normalized = recipe(spec['recipe'], files, roots)
    recipe_key = identity(RECIPE_SCHEMA, normalized)
    execution = attempt(spec['attempt'], recipe_key, spec['block'], normalized['acceptance'],
                        files, files[normalized['proof']]['sha256'])
    return {'recipe': normalized, 'recipe_key': recipe_key, 'attempt': execution,
            'attempt_key': identity(ATTEMPT_SCHEMA, execution)}


def normalize(spec):
    """Pluggable result_cache key function. No run diagnostics enter this value."""
    return build_keys(spec)['attempt']


def artifact_key(manifest):
    fields(manifest, {'schema', 'attempt_key', 'status', 'acceptance', 'files'})
    if manifest['schema'] != ARTIFACT_SCHEMA or manifest['status'] not in {'closed', 'open'}:
        raise ValueError('The artifact manifest has an unsupported schema or status.')
    sha256(manifest['attempt_key'])
    acceptance(manifest['acceptance'])
    if not isinstance(manifest['files'], list) or not manifest['files']:
        raise ValueError('The artifact manifest has no output files.')
    names = set()
    for row in manifest['files']:
        fields(row, {'id', 'sha256'})
        if string(row['id']) in names:
            raise ValueError('The artifact manifest repeats an output file.')
        names.add(row['id'])
        sha256(row['sha256'])
    normalized = {**manifest, 'files': sorted(manifest['files'], key=lambda row: row['id'])}
    return identity(ARTIFACT_SCHEMA, normalized)
