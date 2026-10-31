"""Run the frozen PORT support waves inside the existing declaration job."""
from concurrent.futures import FIRST_COMPLETED, ThreadPoolExecutor, wait
from pathlib import Path
import hashlib
import json
import os
import subprocess
import sys
import threading
import uuid

AUTHORITY = {'path':'/home/cody/zesislar/_build/agents/worker-build-2/PORT-union-v2/DEPENDENCY-BATCH-v1.json',
             'sha256':'5db4af5a27f0e9009cd9f6eb3f3246f2e390bca744ee923c7496d1e8dc4684eb'}
GIB = 1024**3


def binding(path):
    path = Path(path).resolve()
    return {'path':str(path),'sha256':hashlib.sha256(path.read_bytes()).hexdigest()}


def read_bound(row):
    if binding(row['path']) != row:
        raise ValueError('A declaration-wave binding changed.')
    return json.loads(Path(row['path']).read_text())


def save(path, value):
    Path(path).write_text(json.dumps(value,indent=2)+'\n')


def fingerprint(flags, workspace):
    words = [word.replace(str(Path(workspace).resolve()),'{workspace}') for word in flags]
    return hashlib.sha256(json.dumps(words,separators=(',',':')).encode()).hexdigest()


def inherit(config):
    """Retain lineage without carrying executable dispatch into a new job."""
    prior = config.pop('dependency_batch',None)
    nested = config.get('proof_runtime',{}).pop('dependency_batch',None)
    return {'removed':prior,'removed_nested':nested,'native_replay_enabled':False}


def for_phase(config, phase):
    spec=config.get('dependency_batch')
    if spec and (phase!='prerequisites' or config.get('declarations_only') is not True):
        raise ValueError('Dependency waves cannot enter native staging.')
    return spec


def plan_for(row):
    if row != AUTHORITY:
        raise ValueError('The declaration-wave plan is not authorized.')
    plan = read_bound(row)
    modules = [item['module'] for item in plan['modules']]
    flat = [name for wave in plan['waves'] for name in wave['modules']]
    if len(modules)!=23 or len(set(modules))!=23 or flat!=modules:
        raise ValueError('The declaration waves do not cover the exact 23 modules.')
    forbidden = set(plan['MCP_only_libraries']) | {'ZesuSsz.Evidence.RuleScratchRules'}
    if any(name in forbidden or '.Proofs.' in name or name.startswith('ZesuSsz.Evidence.') for name in modules):
        raise ValueError('A protected module enters a dependency wave.')
    expected = [('ZesuSsz.Automation.Hooks','ZesuSsz.Automation.Finish'),
                ('ZesuSsz.Automation.All',None)]
    if len(plan['waves'])!=2 or any((wave.get('after_MCP'),wave.get('before_MCP'))!=pair
                                  for wave,pair in zip(plan['waves'],expected)):
        raise ValueError('The declaration-wave barriers changed.')
    if plan['claim_bytes']!=24*GIB or plan['fence_bytes']!=64*GIB:
        raise ValueError('The declaration-wave memory policy changed.')
    for key in ['guard','compile_measure_helper','run_registry','compiler','dune']:
        if binding(plan[key]['path'])!=plan[key]:
            raise ValueError('A declaration-wave tool changed: '+key)
    return plan


def validate_projection(context, workspace, ordered, spec):
    if set(context)!={'phase','canonical_admission','native_route','control_session',
                      'physical_flags','module_files','build_dir','dependency_batch'}:
        raise ValueError('The execution dependency context has missing or extra fields.')
    if context['dependency_batch']!=spec:
        raise ValueError('The execution dependency context names another wave specification.')
    return validate(context,workspace,ordered,spec)


def validate(runtime, workspace, ordered, spec):
    workspace = Path(workspace).resolve()
    plan = plan_for(spec['plan'])
    if runtime.get('phase')!='prerequisites' or spec.get('declarations_only') is not True:
        raise ValueError('Dependency waves require a declaration-only prerequisite job.')
    admission = runtime.get('canonical_admission',{})
    if admission.get('minimum_claim_bytes')!=24*GIB or admission.get('physical_fence_bytes')!=64*GIB:
        raise ValueError('Dependency waves require the unchanged 24/64 GiB policy.')
    if runtime.get('native_route') or runtime.get('control_session'):
        raise ValueError('A native or interactive route cannot dispatch dependency waves.')
    if fingerprint(runtime['physical_flags'],workspace)!=spec['flags_sha256']:
        raise ValueError('The declaration-wave compiler flags changed.')
    for relative,key in [('tools/resource_guard.sh','guard'),
                         ('tools/block/dependency_compile_measure.py','compile_measure_helper'),
                         ('tools/run_registry.py','run_registry')]:
        if binding(workspace/relative)['sha256']!=plan[key]['sha256']:
            raise ValueError('The staged declaration-wave tool changed: '+key)
    sources = {row['module']:row for row in plan['modules']}
    manifest = read_bound(plan['source_boundary'])
    protected = {row['module']:row for row in manifest['source_rows']}
    for module in plan['MCP_only_libraries']:
        if binding(workspace/runtime['module_files'][module])['sha256']!=protected[module]['sha256']:
            raise ValueError('A protected MCP library source changed: '+module)
    for module,row in sources.items():
        source = workspace/runtime['module_files'][module]
        if not source.resolve().is_relative_to(workspace) or binding(source)['sha256']!=row['source']['sha256']:
            raise ValueError('A dependency-wave source changed: '+module)
        if 'zesu_block.' in source.read_text():
            raise ValueError('A native proof entered a dependency wave.')
    graph = read_bound(spec['graph'])
    actual_edges = {(row['from'],row['to']) for row in graph['import_edges']}
    checked = set(sources)|set(plan['MCP_only_libraries'])
    expected_edges = {(row['from'],row['to']) for row in plan['dependency_edges']}
    if {(left,right) for left,right in actual_edges if left in checked and right in checked}!=expected_edges:
        raise ValueError('The declaration-wave dependency edges changed.')
    positions = {name:index for index,name in enumerate(ordered)}
    if len(positions)!=len(ordered):
        raise ValueError('A declaration module repeats.')
    for wave in plan['waves']:
        members = [name for name in wave['modules'] if name in positions]
        if not members:
            continue
        first,last = min(positions[name] for name in members),max(positions[name] for name in members)
        for barrier,earlier in [(wave['after_MCP'],True),(wave.get('before_MCP'),False)]:
            if barrier is None:
                continue
            if barrier in positions:
                if not (positions[barrier]<first if earlier else last<positions[barrier]):
                    raise ValueError('A declaration wave crossed an MCP barrier.')
            elif not (workspace/runtime['module_files'][barrier]).with_suffix('.vo').is_file():
                raise ValueError('A completed MCP barrier object is absent.')
        for left,right in actual_edges:
            if left in members and right in positions and right not in members and positions[right]>=first:
                raise ValueError('A declaration wave crossed an unfinished dependency.')
        if any(positions[right]>=positions[left] for left,right in actual_edges
               if left in members and right in members):
            raise ValueError('A dependency-wave order is not topological.')
    return plan,graph


def attach(config, row):
    if not config.get('declarations_only'):
        raise ValueError('Dependency waves cannot enter native preparation.')
    pre = config['jobs'][0]
    spec = {'plan':row,'graph':config['cache_import_graph'],'declarations_only':True,
            'flags_sha256':fingerprint(config['physical_flags'],config['prepared_workspace'])}
    runtime = dict(config['proof_runtime'],phase=pre['phase'],native_route=config.get('native_route'),
        control_session=config.get('control_session'),physical_flags=config['physical_flags'],
        canonical_admission={'minimum_claim_bytes':pre['claim_bytes'],
                             'physical_fence_bytes':pre['physical_fence_bytes']})
    validate(runtime,config['prepared_workspace'],pre['ordered_modules'],spec)
    config['dependency_batch']=spec
    return plan_for(row)


def worker_limit(plan, available_bytes):
    peak = plan['parallelism']['rounded_worker_budget_bytes']
    if type(peak) is not int or peak<=0:
        raise ValueError('The dependency worker budget is invalid.')
    limit = min(plan['parallelism']['maximum_workers'],32,
                7*available_bytes//(10*peak),7*(64*GIB)//(10*peak))
    if limit<1:
        raise ValueError('The available memory cannot admit one dependency worker.')
    return limit


def module_command(plan, runtime, workspace, recorder, record):
    # Dune can choose another startup cwd. The bound shim sets the physical cwd.
    shim = ('import os,runpy,sys; os.chdir(sys.argv[1]); '
            'sys.argv=sys.argv[2:]; runpy.run_path(sys.argv[0],run_name="__main__")')
    return [plan['dune']['path'],'exec','--no-build','--root',str(workspace),
            '--build-dir',str(workspace/runtime['build_dir']),'--',sys.executable,'-B','-c',shim,
            str(record),str(recorder),str(record)]


def compile_one(module, plan, graph, runtime, workspace, output, record_root, environment, runner):
    if fingerprint(runtime['physical_flags'],workspace)!=runtime['dependency_batch']['flags_sha256']:
        raise ValueError('The physical dependency flags changed before compilation.')
    for key in ['compiler','dune']:
        if binding(plan[key]['path'])!=plan[key]:
            raise ValueError('A physical dependency tool changed: '+key)
    for relative,key in [('tools/resource_guard.sh','guard'),
                         ('tools/block/dependency_compile_measure.py','compile_measure_helper'),
                         ('tools/run_registry.py','run_registry')]:
        if binding(workspace/relative)['sha256']!=plan[key]['sha256']:
            raise ValueError('A staged physical dependency tool changed: '+key)
    source = workspace/runtime['module_files'][module]
    wanted = next(row['source']['sha256'] for row in plan['modules'] if row['module']==module)
    if binding(source)['sha256']!=wanted:
        raise ValueError('The dependency source changed before compilation: '+module)
    record = record_root/module
    record.mkdir()
    dependencies=[]
    for name in sorted({edge['to'] for edge in graph['import_edges'] if edge['from']==module}):
        dep = workspace/runtime['module_files'][name]
        dependencies.append({'module':name,'source':binding(dep),'object':binding(dep.with_suffix('.vo'))})
    physical = [plan['compiler']['path'],*runtime['physical_flags'],str(source)]
    value = {'physical_argv':physical,'owned_workspace':str(workspace),'source':binding(source),
        'compiler':plan['compiler'],'target':{'module':module,'theorem':'module-compilation'},
        'command_phase':'setup','dependencies':dependencies,'expected_cwd':str(record)}
    save(record/'INPUT.json',value)
    save(record/'PREPARED-INPUT.json',value)
    argv = module_command(plan,runtime,workspace,workspace/'tools/block/dependency_compile_measure.py',record)
    save(record/'LAUNCH.json',{'argv':argv,'cwd':str(record),'environment_inherited':True})
    with (record/'stdout').open('wb') as stdout,(record/'stderr').open('wb') as stderr:
        reply = runner(argv,cwd=record,env=environment,stdout=stdout,stderr=stderr,check=False)
    if reply.returncode:
        raise RuntimeError('The dependency compiler failed: '+module+' (receipt '+str(record)+')')
    result = json.loads((record/'PHYSICAL-RESULT.json').read_text())
    actual = read_bound(result['input'])
    if (result['input']['path']!=str(record/'INPUT.json') or result['returncode']!=0
            or result['physical_argv']!=physical or actual['cwd']!=str(record)
            or actual['physical_argv']!=physical or actual['owned_workspace']!=str(workspace)
            or actual['source']!=binding(source) or actual['compiler']!=plan['compiler']):
        raise ValueError('The physical dependency compiler identity or cwd changed.')
    for dep in dependencies:
        if binding(dep['source']['path'])!=dep['source'] or binding(dep['object']['path'])!=dep['object']:
            raise ValueError('A physical dependency changed during compilation.')
    obj,glob = source.with_suffix('.vo'),source.with_suffix('.glob')
    if binding(source)['sha256']!=wanted or '\nF'+module+'\n' not in glob.read_text():
        raise ValueError('The compiled dependency source or logical owner changed.')
    receipt = {'source':str(source),'source_sha256':wanted,'object':str(obj),
        'object_sha256':binding(obj)['sha256'],'globalization':binding(glob),
        'result':{'success':True,'method':'guarded-dune-dependency-build'},
        'physical_input':result['input'],'prepared_input':binding(record/'PREPARED-INPUT.json'),
        'physical_result':binding(record/'PHYSICAL-RESULT.json'),'launch':binding(record/'LAUNCH.json'),
        'actual_cwd':actual['cwd'],'dependencies':dependencies,
        'stdout':binding(record/'stdout'),'stderr':binding(record/'stderr')}
    save(output/('dependency-'+module+'.json'),receipt)
    return receipt


def run_wave(index, runtime, workspace, output, ordered, completed, environment, runner=None, recheck=None):
    """Finish healthy children after failure, but never dispatch a later module."""
    workspace,output = Path(workspace).resolve(),Path(output).resolve()
    spec = runtime['dependency_batch']
    plan,graph = validate(runtime,workspace,ordered,spec)
    wave = plan['waves'][index]
    members = [name for name in wave['modules'] if name in ordered and name not in completed]
    available = next(int(line.split()[1])*1024 for line in Path('/proc/meminfo').read_text().splitlines()
                     if line.startswith('MemAvailable:'))
    count = worker_limit(plan,available)
    jobs = subprocess.run([str(workspace/'tools/resource_guard.sh'),'jobs'],
        env=environment,capture_output=True,text=True,check=True)
    count = min(count,int(jobs.stdout.strip()))
    if count<1:
        raise ValueError('The unchanged guard permits no dependency worker.')
    root = workspace/'.dependency-records'/uuid.uuid4().hex
    root.mkdir(parents=True)
    receipt_path = output/('DEPENDENCY-WAVE-'+str(index)+'.json')
    pending=set(members);active={};done=set(completed);receipts={};failures=[]
    halt=threading.Event()
    dependencies={name:{edge['to'] for edge in graph['import_edges']
                        if edge['from']==name and edge['to'] in members} for name in members}
    def checkpoint():
        save(receipt_path,{'wave':index,'plan':spec['plan'],'workers':count,
            'completed':sorted(receipts),'failures':failures,'pending':sorted(pending),
            'active':sorted(active.values()),'healthy_children_are_not_stopped':True})
    def compile_ready(name):
        if halt.is_set():
            raise RuntimeError('The dependency did not start after another module failed.')
        try:
            return compile_one(name,plan,graph,runtime,workspace,output,root,
                               environment,runner or subprocess.run)
        except BaseException:
            halt.set()
            raise
    checkpoint()
    with ThreadPoolExecutor(max_workers=count) as pool:
        while pending or active:
            if not failures and not halt.is_set():
                ready=sorted(name for name in pending if dependencies[name]<=done)
                for name in ready[:count-len(active)]:
                    if halt.is_set():break
                    if recheck is not None:
                        try:
                            recheck()
                        except Exception as error:
                            failures.append({'error':str(error)})
                            break
                    pending.remove(name)
                    future=pool.submit(compile_ready,name)
                    active[future]=name
                if pending and not active:
                    failures.append({'error':'The dependency wave has no ready module.'})
            if not active:
                break
            finished,_=wait(active,return_when=FIRST_COMPLETED)
            for future in finished:
                name=active.pop(future)
                try:
                    receipts[name]=future.result();done.add(name)
                except Exception as error:
                    failures.append({'module':name,'error':str(error)})
            checkpoint()
    checkpoint()
    completed.update(receipts)
    if failures:
        raise RuntimeError('The declaration dependency wave failed; later dispatch stopped: '+str(receipt_path))
    return receipts
