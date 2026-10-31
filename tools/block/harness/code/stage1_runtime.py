"""Use fresh typed inputs and the stock lifecycle for Stage1 cache dispatch."""
from copy import deepcopy
import os
from pathlib import Path
import resource
import subprocess
import sys
import time
import uuid

import collector
import kernel_recheck
import launch_adapter
import proof_cache_key as keys
import prospective_inputs
from installed_mappings import InstalledMappings
import result_cache
import transport_mapping
from entry_chain import binding, check_bindings, digest, read_bound, save, strict_loads
from check_entry_outside import reserve, release, ticks, identity_alive, closed_aggregate, clean_environment

W = Path(__file__).resolve().parents[4]
OPAM = Path('/home/cody/islaris/_opam')
HERE = Path(__file__).resolve().parent


def literal(value):
    return {'kind': 'literal', 'value': str(value)}


def roots(out, workspace):
    return [{'role': role, 'path': str(path)} for role, path in [
        ('workspace', workspace), ('attempt_outputs', out), ('runtime_code', HERE),
        ('tooling', W / 'tools'), ('opam', OPAM),
        ('python_install', Path(sys.executable).resolve().parent.parent),
        ('mcp_venv', Path('/home/cody/.local/share/uv/tools/rocq-mcp')),
        ('harness', HERE.parent),
        ('system', Path('/'))]]


def typed_path(path, declared):
    path = Path(path).absolute()
    choices = [(len(Path(row['path']).resolve().parts), row['role']) for row in declared
               if path.resolve().is_relative_to(Path(row['path']).resolve())]
    return {'kind': 'path', 'value': str(path), 'root_role': max(choices)[1]}


def owned_tmpdir(out, declared):
    directory = Path(out) / 'tmp'
    if directory.is_symlink():
        raise ValueError('The owned temporary directory is a symbolic link.')
    directory.mkdir(mode=0o700, exist_ok=True)
    value = typed_path(directory, declared)
    if (value['root_role'] != 'attempt_outputs' or directory.stat().st_uid != os.getuid()
            or not directory.resolve().is_relative_to(Path('/home'))):
        raise ValueError('The temporary directory leaves its owned /home output.')
    return value


def typed_flags(flags, declared):
    result, index, load_paths = [], 0, []
    while index < len(flags):
        word = flags[index]
        result.append(literal(word)); index += 1
        if word in {'-Q', '-R', '-I', '-coqlib'}:
            path = typed_path(flags[index], declared); result.append(path); index += 1
            prefix = ''
            if word in {'-Q', '-R'}:
                prefix = flags[index]; result.append(literal(prefix)); index += 1
            root = next(Path(row['path']).resolve() for row in declared if row['role'] == path['root_role'])
            load_paths.append({'flag': word, 'physical_root_role': path['root_role'],
                               'relative_path': Path(path['value']).resolve().relative_to(root).as_posix(),
                               'logical_prefix': prefix, 'ordinal': len(load_paths)})
    return result, load_paths


def file_row(name, path, kind='source'):
    return dict(binding(path), id=name, kind=kind)


def installed_mapping_inventory(installed, declared):
    """Keep the mapping receipt stable across equivalent owned workspaces."""
    def canonical(path):
        path = Path(path).resolve()
        matches = [(len(Path(row['path']).resolve().parts), row['role'], Path(row['path']).resolve())
                   for row in declared if path.is_relative_to(Path(row['path']).resolve())]
        _, role, root = max(matches)
        return {'root_role': role, 'relative_path': path.relative_to(root).as_posix()}

    def mapping(row):
        return dict(row, root=canonical(row['root']))

    inventory = installed.inventory()
    return {'schema': 'compiled-library.typed-mappings.v2',
            'resolver': dict(inventory['resolver'], path=canonical(inventory['resolver']['path'])),
            'resolutions': [dict(row, source=canonical(row['source']), object=canonical(row['object']))
                            for row in inventory['resolutions']],
            'roots': [mapping(row) for row in inventory['roots']],
            'modules': [dict(row, mapping=mapping(row['mapping']),
                             source=canonical(row['source']), object=canonical(row['object']))
                        for row in inventory['modules']]}


def build_collection(config, job, out, runtime, workspace, scope_binding):
    """Create a fresh complete input after shared prerequisites exist."""
    from memory_policy import attempt_for_job
    config=deepcopy(config)
    config['cache_attempt']=attempt_for_job(config['cache_attempt'],job)
    if runtime.get('declaration_checks') or runtime.get('control_session') is not None:
        raise ValueError('Control sessions cannot enter the native proof route.')
    if runtime.get('dependency_batch') is not None:
        raise ValueError('Dependency waves cannot enter the native proof collection.')
    declared = roots(out, workspace)
    target = runtime['target']['block']
    projection = out / 'prospective/SEMANTIC-PROJECTION.json'
    # The commit-time tests audit the actual consumers. Runtime values still
    # pass the typed projection and prospective collection below.
    save(projection, {'schema': 'entry-chain.runtime-semantic-projection.v1',
                     'provider_fields': transport_mapping.FIELD_MAPPING,
                     'scope_roles': config['cache_attempt']['scope_limits'],
                     'phase': 'native', 'module': target['module'],
                     'proof_source_sha256': target['source_sha256'],
                     'statement_sha256': target['statement_sha256']})
    backend_paths = list(sorted(HERE.glob('*.py'))) + [workspace / rel for rel in [
        'tools/entry_chain_coqc.sh', 'tools/resource_guard.sh', 'tools/coqc_findlib.py',
        'tools/block/entry_chain_compiler.py', 'tools/block/stock_scope_stdin_relay.py',
        'tools/block/complete_goals_mcp.py']]
    backend = [file_row('backend:' + str(index), path) for index, path in enumerate(backend_paths)]
    backend.append(file_row('runtime-semantic-projection', projection))
    backend.append(file_row('python-venv-configuration',Path(sys.prefix)/'pyvenv.cfg'))
    if config.get('dependency_resolution_cache'):
        cached=config['dependency_resolution_cache'];read_bound(cached)
        backend.append(file_row('dependency-resolution-cache',Path(cached['path']),'configuration'))
    semantic_ids = [row['id'] for row in backend]
    runtime_binding = dict(binding(out / 'RUNTIME.json'), root_role='attempt_outputs')
    def transport(encoding, bound, role, selector=None):
        row = {'kind': 'transport', 'role': role, 'encoding': encoding, 'binding': bound,
               'semantic_projection': 'runtime-semantic-projection', 'semantic_dependencies': semantic_ids}
        if selector is not None: row['selector'] = selector
        return row
    env = {name: literal(value) for name, value in {
        'LANG': 'C', 'LC_ALL': 'C', 'LC_CTYPE': 'C', 'PYTHONHASHSEED': '0',
        'PYTHONNOUSERSITE': '1', 'PYTHONDONTWRITEBYTECODE': '1', 'PYTHONCOERCECLOCALE': '0', 'PYTHONUTF8': '1',
        'USER': 'cody', 'LOGNAME': 'cody', 'ROCQ_DUNE_BUILD': '0', 'ROCQ_COMPILE_MULTI_ERROR_CAP': '0',
        'ROCQ_QUERY_TIMEOUT_CAP': '604800', 'ROCQ_PET_TIMEOUT': '604800',
        'ZESU_IN_BATCH': '1', 'ZESU_HOLD_GIB':'180',
        **__import__('memory_policy').environment(job['phase'],job['claim_bytes'],job=job)}.items()}
    for name, path in {'HOME': '/home/cody', 'XDG_RUNTIME_DIR': '/run/user/1000',
                       'OPAM_SWITCH_PREFIX': OPAM, 'ROCQ_WORKSPACE': workspace,
                       'ROCQ_COQC_BINARY': workspace / runtime['coqc_wrapper'],
                       'ZESU_COMPLETE_GOAL_DIR': out / 'native/complete-goals',
                       'AGENT_BUILD_DIR': workspace / runtime['build_dir']}.items():
        env[name] = typed_path(path, declared)
    env['TMPDIR'] = owned_tmpdir(out, declared)
    path_values = {'PATH': [OPAM / 'bin', Path('/usr/local/bin'), Path('/usr/bin'), Path('/bin')],
                   'COQPATH': [], 'OCAMLPATH': [Path(part) for part in runtime['ocamlpath'].replace('{workspace}', str(workspace)).split(':') if part],
                   'CAML_LD_LIBRARY_PATH': [path for path in [OPAM / 'lib/stublibs', OPAM / 'lib/ocaml/stublibs'] if path.is_dir()]}
    for name, paths in path_values.items():
        env[name] = {'kind': 'paths', 'values': [typed_path(path, declared) for path in paths]}
    env['ENTRY_CHAIN_RUNTIME_JSON'] = transport('json-path', runtime_binding, 'runtime-envelope')
    env['ENTRY_CHAIN_RUNTIME_SHA256'] = transport('sha256', runtime_binding, 'runtime-envelope')
    env['ZESU_AGGREGATE_SLICE'] = transport('json-field', dict(scope_binding, root_role='attempt_outputs'),
                                            'aggregate-scope', ['aggregate', 'slice'])
    argv, paths = typed_flags(runtime['physical_flags'], declared)
    prefixes = [typed_path(path, declared) for path in [
        HERE, W / 'tools/block', W / 'tools']]
    launcher = [word.replace('{workspace}', str(workspace)) for word in runtime['mcp_argv']]
    launcher_typed = [typed_path(word, declared) if word.startswith('/') else literal(word) for word in launcher]
    configuration = {'argv': argv, 'load_paths': paths, 'cwd': typed_path(workspace, declared),
                     'environment': env, 'execution_vectors': [
                         {'role': 'python-search-prefix', 'argv': prefixes, 'cwd': typed_path(workspace, declared)},
                         {'role': 'mcp', 'argv': launcher_typed, 'cwd': typed_path(workspace, declared)},
                         {'role': 'mcp-compiler-request', 'argv': typed_flags(runtime['expected_mcp_flags'],declared)[0], 'cwd': typed_path(workspace, declared)},
                         {'role': 'provider', 'argv': [typed_path(sys.executable, declared), literal('-B'), typed_path(HERE / 'entry_chain_provider.py', declared)], 'cwd': typed_path(workspace, declared)}],
                     'init_file_policy': 'disabled with -q', 'warnings_as_errors': [],
                     'native_compilation': 'ondemand', 'proof_skipping': False, 'locale': 'C',
                     'python_version': sys.version.split()[0], 'python_hash_seed': '0', 'solver_seeds': {}}
    from native_instruction_profile import prepare_launch
    launch_plan = prepare_launch(job, runtime['target'], workspace, out / 'native', launcher,
        collector.effective_environment(configuration, keys.roots_by_role(declared)))
    launch_path = out / 'prospective/MCP-LAUNCH.json'
    if launch_path.exists():
        raise ValueError('The prospective MCP launch selection already exists.')
    save(launch_path, launch_plan)
    launch_binding = binding(launch_path)
    selected_vector = [typed_path(word, declared) if word.startswith('/') else literal(word)
                       for word in launch_plan['argv']]
    next(row for row in configuration['execution_vectors'] if row['role'] == 'mcp')['argv'] = selected_vector
    graph = read_bound(config['cache_import_graph'])
    installed = InstalledMappings(runtime['physical_flags'], coqdep=OPAM / 'bin/coqdep',
                                  receipt_dir=out / 'prospective/import-resolution')
    if config.get('dependency_resolution_cache'):
        if not runtime.get('native_route'):raise ValueError('Seed mapping reuse requires an exact minimal authority.')
        from native_route import authority
        from minimal_prefix import common
        from mapping_snapshot import load as load_snapshot
        packet=authority(runtime['native_route']);prefix=common(packet['common_prefix'])
        changes={str(workspace/runtime['module_files'][target['module']]):{'source_sha256':target['source_sha256']}}
        for row in prefix['modules']:
            if row['module']=='ZesuSsz.Evidence.RuleScratchRules':
                changes[str(workspace/runtime['module_files'][row['module']])]={'source_sha256':row['source']['sha256'],'object_sha256':row['object']['sha256']}
        load_snapshot(installed,config['dependency_resolution_cache'],workspace,changes)
    installed.scan_sources()
    imported, _ = prospective_inputs.imported_closure(target['module'], graph)
    for name in imported:
        if name in runtime['module_files']:
            source = workspace / runtime['module_files'][name]
            installed.register_source(source.read_text(), source)
    for name in imported:
        prospective_inputs.module_source(name, runtime, workspace, installed)
    mapping_path = out / 'prospective/INSTALLED-LIBRARY-MAPPINGS.json'
    save(mapping_path, installed_mapping_inventory(installed, declared))
    backend.append(file_row('installed-library-mappings', mapping_path, 'configuration'))
    producer = config['cache_producer_files']
    role_files = {name: [] for name in ['compiler', 'ocaml_runtime', 'standard_library', 'pet', 'coq_lsp',
                                       'mcp', 'python', 'python_dependencies', 'plugins', 'solvers', 'dynamic_libraries']}
    role_files['compiler'] = [file_row('tool:coqc', OPAM / 'bin/coqc', 'binary'), file_row('tool:coqchk', OPAM / 'bin/coqchk', 'binary'), file_row('tool:coqdep', OPAM / 'bin/coqdep', 'binary')]
    role_files['pet'] = [file_row('tool:pet', OPAM / 'bin/pet', 'binary')]
    role_files['python'] = [file_row('tool:python', Path(sys.executable).resolve(), 'binary')]
    role_files['dynamic_libraries'] = [file_row('telemetry:executable:' + str(index),
        row['path'], 'binary') for index, row in enumerate(launch_plan['executable_inputs'])]
    spec = prospective_inputs.build(block=job['key'], runtime=runtime, workspace=workspace, graph=graph,
        roots=declared, configuration=configuration, attempt=deepcopy(config['cache_attempt']),
        backend_files=backend, producer_files=producer, toolchain_files=role_files, installed=installed)
    trees = [{'path': str(path), 'role': role} for path, role in [
        (OPAM / 'lib', 'ocaml_runtime'), (OPAM / 'lib/coq/theories', 'standard_library'),
        (OPAM / 'lib/coq-lsp', 'coq_lsp'), (HERE, 'mcp'),
        (HERE, 'mcp'), (W / 'tools', 'mcp'),
        (Path(sys.base_prefix) / 'lib/python3.12', 'python_dependencies'),
        (Path('/home/cody/.local/share/uv/tools/rocq-mcp/lib/python3.12'), 'python_dependencies')]]
    for path in path_values['OCAMLPATH']:
        trees.append({'path': str(path), 'role': 'plugins'})
    policy = {'schema': collector.SCHEMA, 'python': collector.binding(sys.executable), 'probe': binding(HERE / 'python_probe.py'),
              'python_entry': binding(HERE / 'entry_chain_provider.py'),
              'python_modules': ['rocq_mcp.server', 'pytanque', 'check_entry', 'entry_chain', 'entry_chain_resources', 'entry_pilot_checker'],
              'python_search_prefix': prefixes, 'ldd': binding('/usr/bin/ldd'), 'trees': trees,
              'cache_directories': [str(workspace)], 'executables': [],
              'module_resolution': [],
              'optional_missing_edges':[{'file':collector.binding(Path(sys.base_prefix)/'lib/python3.12/lib-dynload/_crypt.cpython-312-x86_64-linux-gnu.so'),'module':'_crypt','soname':'libcrypt.so.1','optional':True}]}
    if runtime.get('seed_binding_reference'):
        from seed_bindings import descriptor
        reference=runtime['seed_binding_reference']
        if descriptor(reference['descriptor']).get('sealed_boundary'):
            policy['sealed_seed']=reference
    if launch_plan['measurement'] is not None:
        perf_index = next(index for index, row in enumerate(launch_plan['executable_inputs'])
                          if row == launch_plan['measurement']['perf_executable'])
        policy['executables'].append({'name': 'perf', 'file_id': 'telemetry:executable:' + str(perf_index)})
    report = collector.collect(spec, policy)
    report['native_profile_transport'] = launch_binding
    return report


def key_for(report):
    return result_cache.build_key(report['input'], key_function=keys.normalize)


def prepare(config, job, out, runtime, workspace):
    directory = out / 'prospective'; directory.mkdir()
    from memory_policy import attempt_for_job
    attempt=attempt_for_job(config['cache_attempt'],job)
    save(directory / 'SCOPE-PHASE1.json', {'aggregate': {'slice': 'not-admitted'}, 'scope_limits': attempt['scope_limits']})
    report = build_collection(config, job, out, runtime, workspace, binding(directory / 'SCOPE-PHASE1.json'))
    save(directory / 'PHASE1.json', report)
    selected = key_for(report); save(directory / 'KEY.json', selected)
    return report, selected


def materialize_inside(out):
    """Bind the real scope and require the same key before starting MCP."""
    first = read_bound(binding(out / 'prospective/PHASE1.json'))
    check_bindings([first['native_profile_transport']])
    collector.revalidate(first)
    selected = read_bound(binding(out / 'prospective/KEY.json'))
    actual_slice = os.environ.get('ZESU_AGGREGATE_SLICE')
    if not actual_slice: raise ValueError('The stock scope has no aggregate slice.')
    envelope = out / 'prospective/SCOPE-PHASE2.json'
    save(envelope, {'aggregate': {'slice': actual_slice}, 'scope_limits': first['scope_limits']})
    spec = deepcopy(first['input'])
    spec['recipe']['configuration']['environment']['ZESU_AGGREGATE_SLICE']['binding'] = dict(binding(envelope), root_role='attempt_outputs')
    policy = deepcopy(first['collector_policy'])
    report = collector.collect(spec, policy)
    report['native_profile_transport'] = first['native_profile_transport']
    if report['execution_environment']['ZESU_AGGREGATE_SLICE'] != actual_slice:
        raise ValueError('The typed transport differs from the actual aggregate slice.')
    actual = key_for(report)
    if actual != selected: raise ValueError('The actual proof environment changes the normalized attempt key.')
    save(out / 'prospective/PHASE2.json', report)
    save(out / 'prospective/KEY-EQUALITY.json', {'equal': True, 'phase1_key': selected['sha256'], 'phase2_key': actual['sha256'],
         'actual_slice_checked': True, 'proof_calls_between_phases': 0})
    environment = out / 'prospective/ACTUAL-ENVIRONMENT.json'
    save(environment, report['execution_environment'])
    save(out / 'prospective/ACTUAL-BOUNDARY.json', {'environment': binding(environment),
         'phase2': binding(out / 'prospective/PHASE2.json'), 'key_equality': binding(out / 'prospective/KEY-EQUALITY.json'),
         'mcp_launch': first['native_profile_transport']})


def kernel_launch(config, job, outer_out, runtime, workspace, argv, controller):
    from memory_policy import apply_job,environment,fence
    job=apply_job(dict(job,phase='kernel'))
    out = outer_out / 'kernel-check'; out.mkdir(exist_ok=False); (out / 'native').mkdir()
    runtime=dict(runtime,phase='kernel')
    save(out / 'KERNEL-ARGV.json', argv)
    kernel_environment=read_bound(binding(outer_out / 'prospective/PHASE1.json'))['execution_environment']
    kernel_environment.update(environment('kernel',job['claim_bytes'],job=job))
    save(out / 'KERNEL-ENVIRONMENT.json',kernel_environment)
    token = uuid.uuid4().hex
    owner = {'pid': os.getpid(), 'startticks': ticks(os.getpid()), 'token': token, 'block': job['key'], 'purpose': 'cached-kernel-check'}
    claim = 'EntryChainKernel_' + job['key'] + '_' + token
    policy = dict(config['admission'], claim_key=claim, minimum_claim_bytes=job['claim_bytes'],physical_fence_bytes=fence('kernel'),memory_job=job,
                  capture_headroom_bytes=0, output_path=str(out), shared_latch=config['shared_latch'])
    runtime['canonical_admission']=policy
    save(out / 'RUNTIME.json', runtime)
    child = None; child_ticks = None; reserved = False; closed = False; code = 1
    try:
        reserve(policy, claim, owner, out / 'ADMISSION.json', recheck=lambda: check_bindings(runtime['bindings'])); reserved = True
        env = clean_environment(); env.update(environment('kernel',job['claim_bytes'],job=job))
        command = controller.outer_argv(workspace, job['key'] + '-kernel', out)
        save(out / 'LAUNCH.json', {'argv': command, 'kernel_argv': argv, 'search_calls': 0})
        with (out / 'stdout').open('wb') as stdout, (out / 'stderr').open('wb') as stderr:
            child = subprocess.Popen(command, cwd=workspace, env=env, stdout=stdout, stderr=stderr, start_new_session=True)
            child_ticks = ticks(child.pid); save(out / 'BATCH-PROCESS.json', {'pid': child.pid, 'startticks': child_ticks}); code = child.wait()
    finally:
        if child is not None and child.poll() is None: child.wait()
        batch = read_bound(binding(out / 'BATCH-IDENTITY.json')) if (out / 'BATCH-IDENTITY.json').exists() else None
        actors = [] if child is None else [{'pid': child.pid, 'startticks': child_ticks, 'ended': not identity_alive(child.pid, child_ticks)}]
        if batch:
            actors.append({'pid': batch['inside_pid'], 'startticks': batch['inside_startticks'], 'ended': not identity_alive(batch['inside_pid'], batch['inside_startticks'])})
        closed = all(row['ended'] for row in actors) and (batch is None or closed_aggregate(batch, child.pid, child_ticks))
        save(out / 'CLOSURE.json', {'owner': owner, 'actors': actors, 'batch_identity': batch, 'all_owned_actors_closed': closed, 'claim_key': claim})
        released = release(policy, claim, owner, binding(out / 'CLOSURE.json')) if reserved and closed else {'released': not reserved, 'bytes': 0}
        save(out / 'RELEASE.json', released)
    cpu = read_bound(binding(out / 'CPU-FINAL.json')) if (out / 'CPU-FINAL.json').exists() else None
    return {'returncode': code, 'all_owned_actors_closed': closed, 'claim_released': released['released'],
            'CPU': cpu, 'claim_key': claim, 'released_bytes': released['bytes'],
            'closure': binding(out / 'CLOSURE.json'), 'release': binding(out / 'RELEASE.json')}


def run_native(config, job, out, controller):
    from restart_bindings import verify_restart_runtime
    verify_restart_runtime(config,HERE.parent)
    from memory_policy import validate_job
    validate_job(job)
    out = Path(out)
    staged=config.get('sealed_native_preparation')
    if staged:
        if staged['job']!=job['key'] or staged['output']!=str(out) or (out/'STARTED.json').exists():
            raise ValueError('The sealed preparation belongs to another or started job.')
        check_bindings([staged['runtime'],staged['phase1'],staged['key']])
    else:out.mkdir(parents=True, exist_ok=False)
    token = uuid.uuid4().hex
    owner = {'token': token, 'pid': os.getpid(), 'startticks': ticks(os.getpid()), 'chain': config['identity'], 'block': job['key']}
    claim = 'EntryChain_' + job['key'] + '_' + token
    policy = dict(config['admission'], claim_key=claim, minimum_claim_bytes=job['claim_bytes'],physical_fence_bytes=job['physical_fence_bytes'],memory_job=job, capture_headroom_bytes=0,
                  output_path=str(out), shared_latch=config['shared_latch'])
    if staged:
        runtime=read_bound(staged['runtime']);workspace=Path(runtime['prepared_workspace'])
        report=read_bound(staged['phase1']);selected=read_bound(staged['key'])
    else:
        runtime, workspace = controller.stage_job(config, dict(job, policy=policy), out)
        report, selected = prepare(config, job, out, runtime, workspace)
    collector.revalidate(report)
    defects = []
    verifications = []
    def defect(row):
        defects.append(row); save(out / ('CACHE-DEFECT-%03d.json' % len(defects)), row)
    def verify(hit):
        if runtime.get('native_route'):raise ValueError('Stock cached verification is not released for the minimal route.')
        current = {'workspace': str(workspace), 'source': binding(workspace / runtime['module_files'][job['target']['module']]),
                   'statement_sha256': job['target']['statement_sha256'], 'module': job['target']['module'],
                   'checker': binding(OPAM / 'bin/coqchk'), 'physical_flags': runtime['physical_flags'],
                   'dependency_modules': report['input']['recipe']['imports']}
        checked=kernel_recheck.verify(hit, current, lambda argv: kernel_launch(config, job, out, runtime, workspace, argv, controller))
        verifications.append(checked)
        save(out/'KERNEL-RECHECK.json',checked)
        return checked
    cached = result_cache.lookup(config['result_cache']['directory'], selected, verify_closed=verify, on_defect=defect,
                                 purpose=config['result_cache']['purpose'])
    if defects:
        for row in verifications:
            physical=row.get('physical_receipt')
            # An unfinished kernel lifecycle cannot authorize fresh dispatch.
            if physical and (not physical.get('all_owned_actors_closed') or not physical.get('claim_released')):
                raise ValueError('The cache kernel-check lifecycle remains open.')
    kernel_output=out/'kernel-check'
    if defects and kernel_output.exists():
        if not (kernel_output/'CLOSURE.json').exists() or not (kernel_output/'RELEASE.json').exists():
            raise ValueError('The cache kernel-check lifecycle lacks closure or release.')
        if not read_bound(binding(kernel_output/'CLOSURE.json'))['all_owned_actors_closed'] or not read_bound(binding(kernel_output/'RELEASE.json'))['released']:
            raise ValueError('The cache kernel-check lifecycle remains open.')
    if cached is not None:
        launch_adapter.retain_hit(out, cached, cached.get('kernel_recheck'))
        return 0 if cached['result']['success'] else 1
    if config.get('require_cache_hit') and not defects:
        raise ValueError('The unchanged replay missed its required cache entry. Search is held.')
    save(out / 'CACHE-MISS.json', {'cache_status': 'fresh', 'historical_seeding': False})
    code = controller.run_stock_job(config, job, out, prepared={'runtime': runtime, 'workspace': workspace, 'owner': owner})
    result = read_bound(binding(out / 'RESULT.json'))
    if result.get('status') in {'passed', 'native_open'}:
        result = launch_adapter.annotate_native_return(result, binding(out / 'native/CALLS.json'),runtime.get('native_route'))
        result.update(cache_status='fresh', cache_defect=bool(defects),proof_source_sha256=runtime['target']['block']['source_sha256']); save(out / 'RESULT.json', result)
        artifacts = [binding(out / name) for name in ['CLOSURE.json', 'RELEASE.json', 'CPU-FINAL.json', 'native/CALLS.json',
                     'native/NATIVE-RESULTS.json', 'prospective/PHASE1.json', 'prospective/PHASE2.json', 'prospective/KEY-EQUALITY.json']]
        stored = result_cache.store(config['result_cache']['directory'], selected, out / 'RESULT.json', artifacts,
                                    purpose=config['result_cache']['purpose'])
        save(out / 'CACHE-STORE.json', stored)
    return code
