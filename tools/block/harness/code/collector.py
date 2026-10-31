import sys,os
sys.dont_write_bytecode=True
os.environ['PYTHONDONTWRITEBYTECODE']='1'
"""Collect prospective inputs before proof admission.

This proposal does not launch a compiler, PET, MCP, or a proof. It creates
no claim and no cache entry. The caller must use the returned environment
unchanged. The caller must revalidate the receipt immediately before admission.
"""
import argparse
import copy
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess

import proof_cache_key as key

SCHEMA = 'proof-cache.prospective-collector-policy.v1'
CACHES = ['.lia.cache', '.nia.cache', '.nra.cache', '.csdp.cache']
NATIVE_ROLES = {'compiler', 'pet', 'ocaml_runtime', 'plugins', 'solvers', 'dynamic_libraries',
                'python', 'python_dependencies', 'standard_library', 'mcp', 'coq_lsp'}


def binding(path):
    path = Path(path)
    return {'path': str(path), 'sha256': key.file_digest(path)}


def checked(binding_row):
    key.fields(binding_row, {'path', 'sha256'})
    path = Path(binding_row['path'])
    if not path.is_absolute() or key.file_digest(path) != binding_row['sha256']:
        raise ValueError('A collector input changed.')
    return path


def effective_environment(configuration, roots):
    result = {}
    for name, value in configuration['environment'].items():
        key.typed_value(value, roots)
        if value['kind'] == 'paths':
            paths = [row['value'] for row in value['values']]
            if any(':' in path for path in paths):
                raise ValueError('An environment path contains a list separator.')
            result[name] = os.pathsep.join(paths)
        elif value['kind'] == 'transport':
            expected = {'ENTRY_CHAIN_RUNTIME_JSON': 'json-path',
                        'ENTRY_CHAIN_RUNTIME_SHA256': 'sha256', 'ZESU_AGGREGATE_SLICE': 'json-field'}
            if expected.get(name) != value['encoding']:
                raise ValueError('The transport variable has no reviewed encoding.')
            if value['encoding']=='json-field':
                selected=key.strict_loads(Path(value['binding']['path']).read_text())
                for component in value['selector']:selected=selected[component]
                if value['selector']!=['aggregate','slice']:raise ValueError('The aggregate selector is not reviewed.')
                result[name]=selected
            else:
                result[name] = value['binding']['path'] if value['encoding'] == 'json-path' else value['binding']['sha256']
        else:
            result[name] = value['value']
    required = {'LANG': 'C', 'LC_ALL': 'C', 'LC_CTYPE': 'C',
                'PYTHONNOUSERSITE': '1', 'PYTHONDONTWRITEBYTECODE': '1',
                'PYTHONCOERCECLOCALE': '0', 'PYTHONUTF8': '1'}
    if any(result.get(name) != value for name, value in required.items()):
        raise ValueError('The explicit Python or locale policy is incomplete.')
    seed = result.get('PYTHONHASHSEED', '')
    if not seed.isdecimal() or not 0 <= int(seed) <= 4294967295:
        raise ValueError('The Python hash seed is not explicit and fixed.')
    if configuration['python_hash_seed'] != seed or configuration['locale'] != 'C':
        raise ValueError('The configuration differs from the effective environment.')
    if result.get('PYTHONPATH') or result.get('LD_PRELOAD'):
        raise ValueError('An unsupported injection path is present.')
    for name in ['COQPATH', 'OCAMLPATH', 'CAML_LD_LIBRARY_PATH', 'PATH']:
        if configuration['environment'].get(name, {}).get('kind') != 'paths':
            raise ValueError('A required search path is not an explicit ordered list.')
    return result


def path_role(path, roots):
    path = Path(path).absolute()
    resolved = path.resolve(strict=True)
    choices = [(len(root.parts), role) for role, root in roots.items()
               if path.is_relative_to(root) and resolved.is_relative_to(root)]
    if not choices:
        raise ValueError('A collected file leaves its declared root.')
    return max(choices)[1]


def python_probe(policy, environment, cwd):
    python = checked(policy['python'])
    probe = checked(policy['probe'])
    entry = checked(policy['python_entry'])
    request = {'entry_directory': str(entry.parent), 'modules': policy['python_modules'],
               'search_prefix': [row['value'] for row in policy['python_search_prefix']]}
    run = subprocess.run([str(python), '-B', str(probe)], input=json.dumps(request),
                         cwd=cwd, env=environment, capture_output=True, text=True,
                         timeout=60, check=False)
    if run.returncode:
        raise ValueError('The Python input probe failed: '+run.stderr.strip())
    return key.strict_loads(run.stdout)


def elf_needs_libraries(path):
    """Check DT_NEEDED before accepting the loader's static-link report."""
    import struct
    data=Path(path).read_bytes()
    if len(data)<64 or data[:4]!=b'\x7fELF' or data[4] not in (1,2) or data[5] not in (1,2):
        raise ValueError('The static-link report has no supported ELF header.')
    endian='<' if data[5]==1 else '>'
    def number(offset,kind):return struct.unpack_from(endian+kind,data,offset)[0]
    wide=data[4]==2
    phoff=number(32,'Q') if wide else number(28,'I')
    entsize=number(54,'H') if wide else number(42,'H')
    count=number(56,'H') if wide else number(44,'H')
    if entsize<(56 if wide else 32) or phoff+entsize*count>len(data):raise ValueError('The ELF program table is incomplete.')
    for index in range(count):
        entry=phoff+index*entsize
        if number(entry,'I')!=2:continue
        offset=number(entry+8,'Q') if wide else number(entry+4,'I')
        size=number(entry+32,'Q') if wide else number(entry+16,'I')
        step=16 if wide else 8
        if offset+size>len(data) or size%step:raise ValueError('The ELF dynamic table is incomplete.')
        for address in range(offset,offset+size,step):
            tag=number(address,'Q' if wide else 'I')
            if tag==0:break
            if tag==1:return True
    return False


def libraries(path, policy, environment, cwd):
    """Inspect trusted ELF inputs with a separately bound ldd executable."""
    tool = checked(policy['ldd'])
    run = subprocess.run([str(tool), str(path)], cwd=cwd, env=environment,
                         capture_output=True, text=True, timeout=60)
    if run.returncode:
        raise ValueError('The ELF dependency inspection failed: ' + run.stderr.strip())
    result = [];unresolved=[]
    for line in run.stdout.splitlines():
        line = line.strip()
        if not line:
            continue
        if line=='statically linked':
            if elf_needs_libraries(path):raise ValueError('The static-link report hides required libraries.')
            continue
        if re.fullmatch(r'linux-vdso\.so\.\d+ \(0x[0-9a-fA-F]+\)', line):
            continue
        missing=re.fullmatch(r'(\S+) => not found',line)
        if missing:
            row=exact_optional_edge(path,missing[1],policy)
            if row is None:raise ValueError('An ELF dependency is unresolved or unsupported for '+str(path)+': '+line)
            unresolved.append(row)
            continue
        match = re.fullmatch(r'(?:(\S+) => )?(/\S+) \(0x[0-9a-fA-F]+\)', line)
        if not match:
            raise ValueError('An ELF dependency is unresolved or unsupported for '+str(path)+': ' + line)
        result.append({'soname': match[1] or Path(match[2]).name, 'path': match[2]})
    return {'ordered_libraries': result, 'unresolved_edges':unresolved, 'raw_stdout': run.stdout, 'raw_stderr': run.stderr,
            'inspector': binding(tool)}


OPTIONAL_CRYPT_SHA256='068215745b8949169c20c69c97e93e6ab278deaea9d7e731d02164cec40d5d40'

def exact_optional_edge(path,soname,policy):
    rows=policy.get('optional_missing_edges',[])
    if len(rows)>1:raise ValueError('Only the reviewed optional crypt edge is permitted.')
    for row in rows:
        key.fields(row,{'file','module','soname','optional'})
        checked(row['file'])
        if row['module']!='_crypt' or row['soname']!='libcrypt.so.1' or row['optional'] is not True or row['file']['sha256']!=OPTIONAL_CRYPT_SHA256:
            raise ValueError('An optional loader edge lacks the exact reviewed identity.')
        if Path(row['file']['path']).resolve()==Path(path).resolve() and soname==row['soname']:
            return {'module':row['module'],'file_sha256':row['file']['sha256'],'soname':soname,'optional':True}
    return None


def cache_census(directories,cwd):
    cwd=Path(cwd).resolve();found={name:[] for name in CACHES};aliases=[]
    for directory in directories:
        root=Path(directory)
        if not root.is_absolute() or not root.is_dir() or not root.resolve().is_relative_to(cwd):
            raise ValueError('An arithmetic cache directory is not private to the workspace.')
        for path in root.rglob('*'):
            if path.is_symlink():
                if not path.resolve(strict=True).is_relative_to(cwd):
                    raise ValueError('A private cache alias leaves its workspace.')
                aliases.append({'path':str(path.absolute()),'target':str(path.readlink())})
            elif path.name in CACHES and path.is_file():found[path.name].append(str(path.absolute()))
    return {name:sorted(set(paths)) for name,paths in found.items()},sorted(aliases,key=lambda row:row['path'])


def collect(specification, policy, *, probe=python_probe, library_resolver=libraries):
    if policy.get('sealed_seed'):
        return collect_sealed(specification,policy,probe=probe)
    policy=copy.deepcopy(policy)
    policy.setdefault('optional_missing_edges',[])
    key.fields(policy, {'optional_missing_edges','schema', 'python', 'probe', 'python_entry', 'python_modules', 'python_search_prefix',
                        'ldd', 'trees', 'cache_directories', 'executables', 'module_resolution'})
    if policy['schema'] != SCHEMA:
        raise ValueError('The collector policy schema is unsupported.')
    spec = key.without_python_bytecode(specification)
    roots = key.roots_by_role(spec['roots'])
    key.checked_files(spec['files'], roots)
    config = spec['recipe']['configuration']
    key.configuration(config, roots)
    prefixes = policy['python_search_prefix']
    for row in prefixes:
        key.path_value(row, roots)
    vectors = [row for row in config['execution_vectors'] if row['role'] == 'python-search-prefix']
    if prefixes and (len(vectors) != 1 or vectors[0]['argv'] != prefixes):
        raise ValueError('The Python search prefix lacks its exact ordered execution vector.')
    environment = effective_environment(config, roots)
    transport_bindings = {}
    for value in config['environment'].values():
        if value['kind'] == 'transport':
            row = value['binding']
            path = str(Path(row['path']).absolute())
            if path in transport_bindings and transport_bindings[path]['sha256'] != row['sha256']:
                raise ValueError('Two transport references name different envelope bytes.')
            transport_bindings[path] = row
    cwd = Path(config['cwd']['value'])
    for name in ['python', 'probe', 'python_entry', 'ldd']:
        checked(policy[name])
    records = {row['id']: row for row in spec['files']}
    nodes = {row['id']: row for row in spec['recipe']['dependencies']}
    paths = {str(Path(row['path']).absolute()): row['id'] for row in spec['files']}
    added = []

    def add(path, role, kind='runtime_file'):
        path = Path(path).absolute()
        if key.excluded_runtime_file(path):
            raise ValueError('An explicit runtime input names a regenerated output.')
        root_role = path_role(path, roots)
        if not path.is_file():
            raise ValueError('A runtime inventory contains a missing file.')
        if str(path) in paths:
            file_id = paths[str(path)]
            if records[file_id]['sha256'] != key.file_digest(path):
                raise ValueError('A runtime input changed during collection.')
        else:
            relative = path.relative_to(roots[root_role]).as_posix()
            file_id = 'runtime:' + root_role + ':' + relative
            if file_id in records:
                raise ValueError('A collected file ID is ambiguous.')
            row = {'id': file_id, 'kind': kind, 'path': str(path),
                   'sha256': key.file_digest(path), 'root_role': root_role}
            if path.is_symlink():
                row['symlink_target'] = path.readlink().as_posix()
            records[file_id] = row
            nodes[file_id] = {'id': file_id, 'requires': []}
            paths[str(path)] = file_id
            added.append(file_id)
        if role and file_id not in spec['recipe']['toolchain'][role]:
            spec['recipe']['toolchain'][role].append(file_id)
        return file_id

    observation = probe(policy, environment, str(cwd))
    if Path(observation['executable']).resolve() != checked(policy['python']).resolve():
        raise ValueError('The Python probe used another interpreter.')
    if observation['environment'] != environment:
        raise ValueError('The Python process changed its effective environment.')
    if observation['version_short'] != config['python_version']:
        raise ValueError('The Python version differs from the configured version.')
    if any(value != 'C' for value in observation['locale'].values()):
        raise ValueError('The effective locale differs from the configured locale.')
    if observation['hash_randomization'] != (int(environment['PYTHONHASHSEED']) != 0):
        raise ValueError('The Python hash policy differs from the configured policy.')
    add(policy['python']['path'], 'python', 'binary')
    add(policy['probe']['path'], None, 'source')
    add(policy['python_entry']['path'], 'mcp', 'source')
    add(policy['ldd']['path'], None, 'inspection_tool')
    module_names = [row['name'] for row in observation['modules']]
    if module_names != policy['python_modules']:
        raise ValueError('The Python module probe changed its ordered requests.')
    for row in observation['modules']:
        add(row['path'], 'python_dependencies', 'source')
    for distribution in observation['distributions']:
        if not distribution['files']:
            raise ValueError('A Python package has no recorded files.')
        for path in distribution['files']:
            if not key.excluded_runtime_file(path):
                add(path, 'python_dependencies')

    tree_receipts = []
    covered = []
    for tree in policy['trees']:
        key.fields(tree, {'path', 'role'})
        path = Path(tree['path'])
        if not path.is_absolute() or not path.is_dir():
            raise ValueError('A runtime tree is not an absolute directory.')
        files = []
        raw_transports = []
        for parent, dirs, names in os.walk(path, followlinks=False):
            dirs[:] = sorted(name for name in dirs if not key.excluded_runtime_file(Path(parent) / name))
            for name in dirs:
                if (Path(parent) / name).is_symlink():
                    raise ValueError('A runtime tree contains an unaudited directory symlink.')
            for name in sorted(names):
                item = Path(parent) / name
                if key.excluded_runtime_file(item):
                    continue
                if str(item.absolute()) in transport_bindings:
                    raw_transports.append(transport_bindings[str(item.absolute())])
                else:
                    files.append(add(item, tree['role']))
        tree_receipts.append({'path': str(path), 'role': tree['role'], 'files': files,
                              'raw_transport_bindings': raw_transports})
        covered.append(path.resolve())
    required_trees = [observation['sysconfig'][name] for name in ['stdlib', 'platstdlib', 'purelib', 'platlib']]
    python_search = []
    for name in observation['sys_path']:
        path = Path(name or cwd)
        if not path.is_absolute():
            raise ValueError('A Python search path is relative.')
        if path.is_dir():
            required_trees.append(str(path))
            python_search.append({'path': str(path), 'kind': 'directory'})
        elif path.is_file():
            python_search.append({'path': str(path), 'kind': 'file',
                                  'file_id': add(path, 'python_dependencies')})
        else:
            python_search.append({'path': str(path), 'kind': 'absent'})
    for name in ['OCAMLPATH', 'CAML_LD_LIBRARY_PATH']:
        required_trees.extend(row['value'] for row in config['environment'][name]['values'])
    missing=[path for path in required_trees if not any(Path(path).resolve().is_relative_to(root) for root in covered)]
    if missing:
        raise ValueError('A Python or OCaml search directory lacks a complete tree inventory: '+repr(missing))

    resolutions = []
    for row in policy['executables']:
        key.fields(row, {'name', 'file_id'})
        if Path(row['name']).name != row['name']:
            raise ValueError('An executable search request is not a plain name.')
        resolved = shutil.which(row['name'], path=environment['PATH'])
        expected = records[row['file_id']]
        if not resolved or Path(resolved).resolve() != Path(expected['path']).resolve():
            raise ValueError('Ordered executable resolution differs from its binding.')
        resolutions.append({'name': row['name'], 'resolved': binding(resolved), 'file_id': row['file_id']})
    module_resolutions = []
    for row in policy['module_resolution']:
        key.fields(row, {'logical_module', 'file_id'})
        candidates = []
        for flag in config['load_paths']:
            prefix = flag['logical_prefix']
            if flag['flag'] in ['-Q', '-R'] and row['logical_module'].startswith(prefix + '.'):
                suffix = row['logical_module'][len(prefix) + 1:].split('.')
                path = roots[flag['physical_root_role']] / flag['relative_path'] / Path(*suffix).with_suffix('.vo')
                if path.is_file():
                    candidates.append(path)
        if len(candidates) != 1 or candidates[0].resolve() != Path(records[row['file_id']]['path']).resolve():
            raise ValueError('Ordered library resolution differs from its binding.')
        module_resolutions.append({'logical_module': row['logical_module'],
                                   'ordered_candidates': [binding(path) for path in candidates]})

    native = []
    required_paths={str(Path(records[file_id]['path']).resolve()) for role in ['compiler','pet','python','plugins'] for file_id in spec['recipe']['toolchain'][role]}
    required_paths.update(str(Path(row['path']).resolve()) for row in observation['modules'])
    required_paths.update(str(Path(records[row['file_id']]['path']).resolve()) for row in policy['executables'])
    for optional in policy['optional_missing_edges']:
        if exact_optional_edge(optional['file']['path'],optional['soname'],policy) is None:raise ValueError('The optional edge is not reviewed.')
        if str(Path(optional['file']['path']).resolve()) in required_paths:
            raise ValueError('A required executable or imported module needs the optional edge.')
    queue = list(dict.fromkeys(name for role in sorted(NATIVE_ROLES) for name in spec['recipe']['toolchain'][role]))
    inspected = set()
    while queue:
        file_id = queue.pop(0)
        path = Path(records[file_id]['path'])
        if path.resolve() in inspected:
            continue
        inspected.add(path.resolve())
        with path.open('rb') as stream:
            header=stream.read(18)
        if not header.startswith(b'\x7fELF'):
            continue
        if len(header)!=18 or header[4] not in (1,2) or header[5] not in (1,2):
            raise ValueError('An ELF input has an unsupported header.')
        elf_type=int.from_bytes(header[16:18],'little' if header[5]==1 else 'big')
        if elf_type==1:
            # ET_REL files cannot execute. Their final linked images are inspected separately.
            continue
        if elf_type not in (2,3):raise ValueError('An ELF input has an unsupported object type.')
        report = library_resolver(path, policy, environment, str(cwd))
        if report.get('unresolved_edges') and str(path.resolve()) in required_paths:
            raise ValueError('A required executable or imported module has an unresolved edge.')
        for row in report['ordered_libraries']:
            new_id = add(row['path'], 'dynamic_libraries', 'binary')
            queue.append(new_id)
        native.append({'file_id': file_id, 'resolution': report})

    for optional in policy['optional_missing_edges']:
        matches=[row for row in native if Path(records[row['file_id']]['path']).resolve()==Path(optional['file']['path']).resolve()]
        if len(matches)!=1:raise ValueError('The optional extension lacks one inspected inventory file.')
        features=spec['recipe']['backend']['features']
        features.update(optional_crypt_sha256=optional['file']['sha256'],optional_crypt_module='_crypt',optional_crypt_soname='libcrypt.so.1',optional_crypt_status='inventory-only-unresolved' if matches[0]['resolution'].get('unresolved_edges') else 'resolved')
    cache_rows = {row['name']: row for row in spec['attempt']['arithmetic_caches']}
    found,aliases=cache_census(policy['cache_directories'],cwd)
    if set(cache_rows) != set(CACHES) or not policy['cache_directories']:
        raise ValueError('The initial arithmetic-cache census is incomplete.')
    for name in CACHES:
        files = sorted(set(found[name]))
        found[name] = files
        row = cache_rows[name]
        if row['policy'] == 'empty-private' and files:
            raise ValueError('An empty-private arithmetic cache already contains data.')
        ids = [add(path, None, 'arithmetic_cache') for path in files if not key.excluded_runtime_file(path)]
        if row['initial_files'] != ids:
            raise ValueError('The arithmetic-cache policy differs from its direct census.')

    # Bind all conservative closure inputs to the proof. The caller supplies
    # the precise source graph; these additional runtime leaves are required.
    proof_node = nodes[spec['recipe']['proof']]
    proof_node['requires'] = list(dict.fromkeys(proof_node['requires'] + added))
    spec['files'] = list(records.values())
    spec['recipe']['dependencies'] = list(nodes.values())
    key.build_keys(spec)  # Validate the frozen schema. Do not create a cache entry.
    return {'schema': 'proof-cache.prospective-collection.v1', 'input': spec,
            'execution_environment': environment, 'Python': observation, 'trees': tree_receipts,
            'Python_search_paths': python_search, 'collector_policy': policy,
            'executables': resolutions, 'module_resolution': module_resolutions,
            'native_library_resolution': native, 'initial_cache_census': found, 'private_aliases': aliases,
            'scope_limits': spec['attempt']['scope_limits'], 'tool_timeouts': spec['attempt']['tool_timeouts'],
            'claims_created': 0, 'proof_calls': 0, 'cache_entries_created': 0,
            'launch_integration_released': False}


def revalidate(report, *, probe=python_probe, library_resolver=libraries):
    """Check retained files, directory inventories, and caches before admission."""
    if report.get('sealed_seed'):
        from seed_bindings import descriptor
        descriptor(report['sealed_seed']['descriptor'])
        spec=report['input'];roots=key.roots_by_role(spec['roots'])
        key.checked_files(spec['files'],roots)
        if effective_environment(spec['recipe']['configuration'],roots)!=report['execution_environment']:
            raise ValueError('The sealed cell launch environment changed.')
        key.build_keys(spec)
        return True
    spec = key.without_python_bytecode(report['input'])
    roots = key.roots_by_role(spec['roots'])
    key.checked_files(spec['files'], roots)
    records = {row['id']: row for row in spec['files']}
    for tree in report['trees']:
        current = set()
        for parent, dirs, names in os.walk(tree['path'], followlinks=False):
            dirs[:] = [name for name in dirs if not key.excluded_runtime_file(Path(parent) / name)]
            if any((Path(parent) / name).is_symlink() for name in dirs):
                raise ValueError('A runtime directory acquired a symlink.')
            current.update(str((Path(parent) / name).absolute()) for name in names
                           if not key.excluded_runtime_file(Path(parent) / name))
        expected = {records[name]['path'] for name in tree['files'] if name in records}
        expected.update(row['path'] for row in tree['raw_transport_bindings']
                        if not key.excluded_runtime_file(row['path']))
        if current != expected:
            raise ValueError('A runtime directory changed after collection.')
    for row in report['Python_search_paths']:
        path = Path(row['path'])
        if (row['kind'] == 'absent' and path.exists()) or (row['kind'] == 'directory' and not path.is_dir()):
            raise ValueError('A Python search path changed after collection.')
    current,aliases=cache_census(report['collector_policy']['cache_directories'],spec['recipe']['configuration']['cwd']['value'])
    if aliases != report.get('private_aliases',[]):
        raise ValueError('A private workspace alias changed after collection.')
    if {k: sorted(set(v)) for k, v in current.items()} != report['initial_cache_census']:
        raise ValueError('An arithmetic cache changed after collection.')
    if effective_environment(spec['recipe']['configuration'], roots) != report['execution_environment']:
        raise ValueError('The frozen launch environment changed.')
    policy = report['collector_policy']
    cwd = spec['recipe']['configuration']['cwd']['value']
    observation = probe(policy, report['execution_environment'], cwd)
    if observation != report['Python']:
        raise ValueError('Python resolution changed before admission.')
    for row in report['native_library_resolution']:
        fresh = library_resolver(Path(records[row['file_id']]['path']), policy,
                                 report['execution_environment'], cwd)
        if fresh['ordered_libraries'] != row['resolution']['ordered_libraries'] or fresh.get('unresolved_edges',[])!=row['resolution'].get('unresolved_edges',[]):
            raise ValueError('Native library resolution changed before admission.')
    key.build_keys(spec)
    return True


def collect_sealed(specification,policy,*,probe=python_probe):
    """Use the sealed inventory and check only explicit cell inputs."""
    from seed_bindings import descriptor,compact_collection,read,installation_path,mutable_execution
    reference=policy['sealed_seed'];value=descriptor(reference['descriptor'])
    if not value.get('sealed_boundary'):raise ValueError('A fast collector has no sealed boundary.')
    # PHASE2 already holds the compact input produced by PHASE1.
    spec=copy.deepcopy(specification)
    if not any(row['id']=='sealed-shared-seed' for row in spec['files']):
        spec=compact_collection(spec,reference)
    roots=key.roots_by_role(spec['roots']);key.checked_files(spec['files'],roots)
    config=spec['recipe']['configuration'];key.configuration(config,roots)
    environment=effective_environment(config,roots)
    observation=probe(policy,environment,config['cwd']['value'])
    seal=read(value['sealed_boundary']);baseline=read(seal['collection'])
    if Path(observation['executable']).resolve()!=checked(policy['python']).resolve():
        raise ValueError('The sealed probe used another interpreter.')
    if observation['environment']!=environment or observation['version_short']!=config['python_version']:
        raise ValueError('The sealed Python configuration changed.')
    if any(item!='C' for item in observation['locale'].values()):raise ValueError('The sealed locale changed.')
    if observation['hash_randomization']!=(int(environment['PYTHONHASHSEED'])!=0):raise ValueError('The sealed hash policy changed.')
    if [row['name'] for row in observation['modules']]!=policy['python_modules']:
        raise ValueError('The sealed module probe changed its ordered requests.')
    if observation['distributions']!=baseline['Python']['distributions'] or observation['sysconfig']!=baseline['Python']['sysconfig']:
        raise ValueError('The frozen shared Python installation changed.')
    explicit={str(Path(row['path']).resolve()) for row in spec['files']}
    recorded=read(seal['external_inventory']);by_path={str(Path(row['path']).resolve()):row for row in recorded}
    external={str(Path(row['path']).resolve()) for row in recorded
              if installation_path(row['path']) and not mutable_execution(row['path'])}
    execution=[row for row in recorded if mutable_execution(row['path'])]
    for row in observation['modules']:
        path=str(Path(row['path']).resolve())
        if path not in explicit|external:
            if path not in by_path:raise ValueError('A Python module lacks a declared cell or frozen source identity.')
            execution.append(by_path[path])
    proof_node=next(row for row in spec['recipe']['dependencies'] if row['id']==spec['recipe']['proof'])
    for row in execution:
        path=str(Path(row['path']).resolve())
        if path in explicit:continue
        identity='cell-execution:'+str(len(spec['files']))
        spec['files'].append(dict(row,id=identity,kind='source',root_role=path_role(row['path'],roots)))
        spec['recipe']['dependencies'].append({'id':identity,'requires':[]});proof_node['requires'].append(identity)
        explicit.add(path)
    for row in observation['modules']:
        if str(Path(row['path']).resolve()) not in explicit|external:
            raise ValueError('A Python module escaped the sealed inventory and explicit cell inputs.')
    found,aliases=cache_census(policy['cache_directories'],config['cwd']['value'])
    for row in spec['attempt']['arithmetic_caches']:
        if row['policy']=='empty-private' and found[row['name']]:raise ValueError('An empty-private cache contains data.')
    key.build_keys(spec)
    return {'schema':'proof-cache.prospective-collection.v1','input':spec,
        'execution_environment':environment,'Python':observation,'trees':[],
        'Python_search_paths':[],'collector_policy':policy,'executables':[],
        'module_resolution':[],'native_library_resolution':[],
        'initial_cache_census':found,'private_aliases':aliases,
        'scope_limits':spec['attempt']['scope_limits'],'tool_timeouts':spec['attempt']['tool_timeouts'],
        'claims_created':0,'proof_calls':0,'cache_entries_created':0,
        'launch_integration_released':False,'sealed_seed':reference}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--input', required=True)
    parser.add_argument('--policy', required=True)
    parser.add_argument('--output', required=True)
    args = parser.parse_args()
    output = Path(args.output)
    policy = key.strict_loads(Path(args.policy).read_text())
    if any(output.resolve().is_relative_to(Path(row['path']).resolve()) for row in policy['trees']):
        raise ValueError('Collector outputs must remain outside runtime trees.')
    output.mkdir(parents=True, exist_ok=False)
    spec = key.strict_loads(Path(args.input).read_text())
    report = collect(spec, policy)
    report['input_bindings'] = [binding(args.input), binding(args.policy), binding(__file__), binding(key.__file__)]
    (output / 'COLLECTION.json').write_text(json.dumps(report, indent=2) + '\n')
    (output / 'INPUT.json').write_text(json.dumps(report['input'], indent=2) + '\n')


if __name__ == '__main__':
    main()
