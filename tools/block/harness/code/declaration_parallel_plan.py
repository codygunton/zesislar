"""Require explicit bounded declaration dispatch without changing native defaults."""
from copy import deepcopy
from pathlib import Path
import re
import shutil

from declaration_dag import CLAIM_BYTES, validate as validate_graph
from declaration_resources import weights
from entry_chain import binding, read_bound
from import_graph import graph_closure


SCHEMA = 'entry-chain.declaration-dag.v1'
PROTECTED = {'ZesuSsz.Automation.Hooks', 'ZesuSsz.Automation.EntryIntro',
             'ZesuSsz.Automation.Finish', 'ZesuSsz.Automation.All',
             'ZesuSsz.Automation.AllLegacy', 'ZesuSsz.Evidence.RuleScratchRules'}


def inherit(config):
    prior = config.pop('declaration_dag', None)
    nested = config.get('proof_runtime', {}).pop('declaration_dag', None)
    return {'removed': prior, 'removed_nested': nested, 'execution_inherited': False}


def arguments(parser):
    parser.add_argument('--parallel-declarations',action='store_true')
    parser.add_argument('--declaration-module-measurements',type=Path)
    parser.add_argument('--declaration-workers',type=int,default=48)


def check_arguments(args, parser):
    if not 1 <= args.declaration_workers <= 48:
        parser.error('Declaration workers must be between 1 and 48.')
    if not args.parallel_declarations and (args.declaration_module_measurements or args.declaration_workers!=48):
        parser.error('Declaration worker options require --parallel-declarations.')
    if args.parallel_declarations and (not getattr(args,'declarations_only',True) or
            getattr(args,'dependency_batch',None) or getattr(args,'control_session',None)):
        parser.error('Parallel dispatch requires declaration-only execution without another dispatcher.')


def references(spec):
    result=[spec['graph'],spec['dune']]+[row['source'] for row in spec['sources']]
    if spec['profile'] is not None:
        result.append(spec['profile'])
        for row in read_bound(spec['profile'])['modules']:
            result.append(row['receipt'])
            receipt=read_bound(row['receipt'])
            if receipt.get('physical_result'):
                result.append(receipt['physical_result'])
    return result


def planning_compiler(config):
    """Use the same bound identity that stage_job selects for the compiler."""
    selected=config['effective_compiler_version']['compiler']
    if (not isinstance(selected,dict) or set(selected)!={'path','sha256'} or
            'physical_compiler' in config and config['physical_compiler']!=selected):
        raise ValueError('The declaration planning compiler differs from its bound effective identity.')
    return dict(selected)


def attach(config, *, measurements=None, maximum_workers=48):
    compiler=planning_compiler(config)
    if (config.get('declarations_only') is not True or config.get('control_session') or
            config.get('dependency_batch') or type(maximum_workers) is not int or
            not 1 <= maximum_workers <= 48):
        raise ValueError('Parallel declarations require an explicit declaration-only route with at most 48 workers.')
    jobs = [row for row in config['jobs'] if row['phase'] == 'prerequisites']
    if len(jobs) != 1:
        raise ValueError('Parallel declarations require one prerequisite job.')
    job = jobs[0]
    if job['claim_bytes'] != CLAIM_BYTES or job['physical_fence_bytes'] != CLAIM_BYTES:
        raise ValueError('Parallel declarations require the public full-fence 64/64 GiB profile.')
    workspace = Path(config['prepared_workspace']).resolve()
    ordered = job['ordered_modules']
    modules = config['proof_runtime']['module_files']
    graph = read_bound(config['cache_import_graph'])
    forward = {}
    for row in graph['import_edges']:
        forward.setdefault(row['from'], set()).add(row['to'])
    completed = graph_closure(ordered, forward) - set(ordered)
    protected, sources = [], []
    native = {row['target']['module'] for row in config['jobs']
              if row.get('phase') == 'native' and (row.get('target') or {}).get('module')}
    for module in ordered:
        source = workspace / modules[module]
        if (not source.resolve().is_relative_to(workspace) or module in native or
                '.Proofs.' in module or re.search(r'\bzesu_block\b', source.read_text())):
            raise ValueError('A native proof cannot enter the declaration DAG.')
        if (module in PROTECTED or '.Evidence.' in module or
                re.search(r'^\s*Declare\s+ML\s+Module\b', source.read_text(), re.M)):
            protected.append(module)
        sources.append({'module': module, 'source': binding(source)})
    resource = weights(ordered, modules, workspace, compiler,
                       config['physical_flags'], measurements)
    validate_graph(ordered, graph['import_edges'], resource['weights'], completed, protected)
    dune = shutil.which('dune')
    if dune is None:
        raise ValueError('Parallel declarations require the existing Dune executable.')
    spec = {'schema': SCHEMA, 'graph': config['cache_import_graph'],
            'sources': sources, 'completed_modules': sorted(completed),
            'protected_modules': protected, 'maximum_workers': maximum_workers,
            'dune': binding(dune), **resource}
    config['declaration_dag'] = spec
    return spec


def for_phase(config, phase, workspace):
    spec = config.get('declaration_dag')
    if spec is None:
        return None
    if config.get('declarations_only') is not True:
        raise ValueError('The declaration DAG cannot enter native execution.')
    if phase != 'prerequisites':
        return None
    copied = deepcopy(spec)
    old = Path(config['prepared_workspace']).resolve()
    workspace = Path(workspace).resolve()
    for row in copied['sources']:
        row['source']['path'] = str(workspace / Path(row['source']['path']).relative_to(old))
    return copied


def validate(runtime, workspace):
    spec = runtime['declaration_dag']
    admission = runtime.get('canonical_admission', {})
    if (spec.get('schema') != SCHEMA or runtime.get('phase') != 'prerequisites' or
            runtime.get('native_route') or runtime.get('control_session') or
            runtime.get('dependency_batch') or
            admission.get('minimum_claim_bytes') != CLAIM_BYTES or
            admission.get('physical_fence_bytes') != CLAIM_BYTES or
            type(spec['maximum_workers']) is not int or not 1 <= spec['maximum_workers'] <= 48):
        raise ValueError('The declaration DAG changed its public phase or fixed policy.')
    if [row['module'] for row in spec['sources']] != runtime['ordered_modules']:
        raise ValueError('The declaration DAG changed its source order.')
    protected=[]
    for row in spec['sources']:
        source = Path(workspace) / runtime['module_files'][row['module']]
        if binding(source) != row['source']:
            raise ValueError('A declaration DAG source changed.')
        text=source.read_text()
        if '.Proofs.' in row['module'] or re.search(r'\bzesu_block\b',text):
            raise ValueError('A native proof cannot enter the declaration DAG.')
        if (row['module'] in PROTECTED or '.Evidence.' in row['module'] or
                re.search(r'^\s*Declare\s+ML\s+Module\b',text,re.M)):
            protected.append(row['module'])
    if protected!=spec['protected_modules']:
        raise ValueError('The declaration DAG changed its protected MCP barriers.')
    resource = weights(runtime['ordered_modules'], runtime['module_files'], workspace,
                       runtime['physical_compiler'], runtime['physical_flags'], spec['profile'])
    if resource['weights'] != spec['weights'] or resource['evidence'] != spec['evidence']:
        raise ValueError('The declaration DAG resource evidence changed.')
    if binding(spec['dune']['path']) != spec['dune']:
        raise ValueError('The declaration DAG Dune executable changed.')
    graph = read_bound(spec['graph'])
    forward={}
    for row in graph['import_edges']:
        forward.setdefault(row['from'],set()).add(row['to'])
    if graph_closure(runtime['ordered_modules'],forward)-set(runtime['ordered_modules'])!=set(spec['completed_modules']):
        raise ValueError('The declaration DAG changed its completed import closure.')
    validate_graph(runtime['ordered_modules'], graph['import_edges'], spec['weights'],
                   spec['completed_modules'], spec['protected_modules'])
    return spec
