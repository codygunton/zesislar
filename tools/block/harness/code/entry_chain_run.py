import sys,os
sys.dont_write_bytecode=True
os.environ['PYTHONDONTWRITEBYTECODE']='1'
import clone_copy
from proof_bindings import check_proof_bindings
"""Run one CPU-unlimited chain job with canonical admission and exact closure."""
import argparse
from copy import deepcopy
import os
from pathlib import Path
import resource
import shlex
import shutil
import subprocess
import sys
import time
import traceback
import uuid

# Load only the versioned metadata adapter from this owned controller directory.
sys.path[1:1] = [str(Path(__file__).resolve().parents[2]), str(Path(__file__).resolve().parents[3])]
import entry_chain_result
if Path(entry_chain_result.__file__).resolve()!=Path(__file__).with_name('entry_chain_result.py').resolve():
    raise ValueError('The versioned metadata adapter has another origin.')

from entry_chain import binding,check_bindings,digest,read_bound,relative,save,strict_loads
from aggregate_layout import aggregate_root
from check_entry_outside import reserve,release,closed_aggregate,ticks,identity_alive,clean_environment
from entry_chain_resources import normalize_cpu,check_operation,publish_latch,validate_limits,effective
from entry_chain_process import sample,identity,ProcessGone

ROOT=Path(__file__).resolve().parents[4]


def ready_claim_priority(config,receipt):
    row=config.get('priority_claim')
    if row is None or Path(receipt).exists():return
    ledger=Path(config['admission']['ledger'])
    # This is a prerequisite observation. The normal reserve check remains locked.
    while True:
        value=strict_loads(ledger.read_text())['fixed_claims'].get(row['key'],0)
        if value>=row['bytes']:
            save(receipt,{'claim':row,'observed_assigned_bytes':value,'time_ns':time.time_ns()})
            return
        if not identity_alive(row['owner_pid'],row['owner_startticks']):
            raise ValueError('The priority owner ended before its assignment was observed.')
        time.sleep(1)


def binding_recheck(config):
    check_proof_bindings(config)
    if Path(config['shared_latch']).exists():
        raise RuntimeError('A shared infrastructure failure holds admission.')


def check_project_paths(workspace):
    """Require complete directives and identical owned imports in both project files."""
    workspace=Path(workspace).resolve();records={};owned={}
    for name in ['_CoqProject','_RocqProject']:
        path=workspace/name;records[name]=[];owned[name]=[]
        for line in path.read_text().splitlines():
            words=shlex.split(line,comments=True)
            if not words:continue
            option=words[0]
            if option not in {'-I','-Q','-R'} or len(words)!=(2 if option=='-I' else 3):
                raise ValueError('A project directive has unsupported syntax.')
            target=Path(words[1])
            target=(workspace/target).resolve() if not target.is_absolute() else target.resolve()
            local=target.is_relative_to(workspace)
            if not local and not target.is_relative_to('/home/cody/islaris/_opam'):
                raise ValueError('A project directive refers to another owned workspace.')
            if not target.is_dir():raise ValueError('A project import directory is absent.')
            row=[option,str(target),*words[2:]];records[name].append(row)
            if local:owned[name].append(row)
    if owned['_CoqProject']!=owned['_RocqProject']:
        raise ValueError('The project files select different owned imports.')
    return {'workspace':str(workspace),'directives':records,'owned_imports_equal':True,
            'all_owned_paths_contained':True,'proof_ran':False}


def install_guard_override(config,workspace,copies):
    override=config['guard_override'];base=config['guard_override_base']
    check_bindings([override] if override == base else [override,base])
    target=workspace/'tools/resource_guard.sh'
    if digest(target)!=base['sha256']:
        raise ValueError('The owned guard base differs from its bound source.')
    positions=[i for i,row in enumerate(copies) if row['owned']['path']==str(target.resolve())]
    if len(positions)!=1:raise ValueError('The owned guard lacks one copy record.')
    before=deepcopy(copies[positions[0]])
    clone_copy.copy2(override['path'],target)
    if digest(target)!=override['sha256'] or (target.stat().st_dev,target.stat().st_ino)==(Path(override['path']).stat().st_dev,Path(override['path']).stat().st_ino):
        raise ValueError('The owned guard copy differs or shares its source inode.')
    copies[positions[0]]={'source':override,'owned':binding(target),'distinct_inode':True,'guard_override':True}
    return {'original_copy':before,'replacement_copy':copies[positions[0]],'diagnostic_limit':64}


def outer_argv(workspace,key,out):
    guard=str(workspace/'tools/resource_guard.sh')
    return [guard,'batch','entry-chain-'+key,'--',guard,'scope','entry-chain-client','--',
            sys.executable,'-B',str(Path(__file__).resolve()),'--inside',str(out)]


def stage_job(config,job,out):
    source=Path(config['prepared_workspace'])
    sealed=False
    if config.get('seed_binding_reference'):
        from seed_bindings import descriptor,validate
        sealed=bool(descriptor(config['seed_binding_reference']['descriptor']).get('sealed_boundary'))
        if sealed:validate(config['seed_binding_reference'],source)
    workspace=source if sealed else out/'workspace'
    if job['phase']=='native':
        readiness=read_bound(config['readiness'])
        check_bindings(readiness['objects'])
    if not sealed:workspace.mkdir()
    copies=[]
    for path in ([] if sealed else source.rglob('*')):
        rel=path.relative_to(source)
        from runtime_ignores import excluded
        if excluded(path):continue
        if path.is_symlink():continue
        if path.is_dir():
            (workspace/rel).mkdir(parents=True,exist_ok=True)
            continue
        if path.name in {'.lia.cache','.nia.cache','.nra.cache','.csdp.cache','.bv_solve.cache'}:continue
        destination=workspace/rel;destination.parent.mkdir(parents=True,exist_ok=True)
        clone_copy.copy2(path,destination)
        if (path.stat().st_dev,path.stat().st_ino)==(destination.stat().st_dev,destination.stat().st_ino):
            raise ValueError('The private job shares a source inode.')
        copies.append({'source':binding(path),'owned':binding(destination),'distinct_inode':True})
    for path in ([] if sealed else source.rglob('*')):
        if not path.is_symlink():continue
        destination=workspace/path.relative_to(source);destination.parent.mkdir(parents=True,exist_ok=True)
        destination.symlink_to(os.readlink(path))
        if not destination.resolve().is_relative_to(workspace):
            raise ValueError('A job import alias leaves its private workspace.')
    for name in ['_CoqProject','_RocqProject']:
        path=workspace/name
        if path.is_file() and not sealed:path.write_text(path.read_text().replace(str(source),str(workspace)))
    project_paths=check_project_paths(workspace)
    save(out/'PROJECT-PATHS.json',project_paths)
    if sealed or config.get('prepared_tool_transition'):
        from restart_bindings import install_restart_tools
        transition=install_restart_tools(workspace,deepcopy(config),Path(__file__).resolve().parent.parent)
        save(out/'RESTART-TOOLS-TRANSITION.json',transition)
        replacements={row['owned']['path']:row for row in transition['copies']}
        copies=[replacements.pop(row['owned']['path'],row) for row in copies]
        copies.extend(replacements.values())
    save(out/'GUARD-OVERRIDE.json',install_guard_override(config,workspace,copies))
    # Each worker uses its own private project, generated objects, and solver cache.
    for rel in ['tools/block/stock_scope_stdin_relay.py','tools/block/entry_chain_compiler.py','tools/block/entry_chain.py',
                'tools/block/entry_chain_resources.py','tools/block/entry_chain_process.py','tools/block/entry_chain_plan.py']:
        target=workspace/rel;target.parent.mkdir(parents=True,exist_ok=True);clone_copy.copy2(Path(__file__).with_name(Path(rel).name),target)
    expected_wrapper=Path(__file__).resolve().parent.parent/'runtime-tools/entry_chain_coqc.sh'
    if digest(workspace/'tools/entry_chain_coqc.sh') != digest(expected_wrapper):
        raise ValueError('The final staged compiler wrapper differs from the bounded physical policy.')
    clone_copy.copy2(Path(__file__).with_name('entry_chain_resources.py'), workspace/'tools/block/entry_chain_resources.py')
    for name in ['entry_chain_compiler.py','compile_measure.py','clone_copy.py','binding_cache.py','compiler_snapshot.py']:
        clone_copy.copy2(Path(__file__).with_name(name),workspace/'tools/block'/name)
        src=Path(__file__).with_name(name);dst=workspace/'tools/block'/name
        record={'source':binding(src),'owned':binding(dst),'distinct_inode':True}
        positions=[i for i,row in enumerate(copies) if row['owned']['path']==str(dst)]
        if positions:copies[positions[0]]=record
        else:copies.append(record)
    clone_copy.copy2(workspace/'tools/run_registry.py',workspace/'tools/block/run_registry.py')
    clone_copy.copy2(Path(__file__).with_name('runtime_ignores.py'),workspace/'tools/block/runtime_ignores.py')
    clone_copy.copy2(Path(__file__).with_name('seed_bindings.py'),workspace/'tools/block/seed_bindings.py')
    helper=Path(__file__).with_name('proof_bindings.py')
    owned_helper=workspace/'tools/block/proof_bindings.py'
    clone_copy.copy2(helper,owned_helper)
    copies.append({'source':binding(helper),'owned':binding(owned_helper),'distinct_inode':helper.stat().st_ino!=owned_helper.stat().st_ino,'new_harness_dependency':True})
    # Import from the physical compiler workspace before starting MCP or a compiler.
    probe="import json,entry_chain_resources,proof_bindings,binding_cache,seed_bindings; proof_bindings.check_proof_bindings({'bindings':[]}); print(json.dumps({'resources':entry_chain_resources.__file__,'proof_bindings':proof_bindings.__file__,'binding_cache':binding_cache.__file__,'seed_bindings':seed_bindings.__file__}))"
    import_env=dict(os.environ,PYTHONPATH=str(workspace/'tools/block')+os.pathsep+str(workspace/'tools'),PYTHONDONTWRITEBYTECODE='1')
    checked=subprocess.run([sys.executable,'-B','-c',probe],cwd=workspace,env=import_env,capture_output=True,text=True)
    save(out/'COMPILER-IMPORT-CONTROL.json',{'argv':[sys.executable,'-B','-c',probe],'returncode':checked.returncode,'stdout':checked.stdout,'stderr':checked.stderr,'compiler_started':False,'proof_calls':0})
    if checked.returncode:raise RuntimeError('The staged compiler dependency import failed.')
    origins=strict_loads(checked.stdout)
    for key,name in [('resources','entry_chain_resources.py'),('proof_bindings','proof_bindings.py'),('binding_cache','binding_cache.py'),('seed_bindings','seed_bindings.py')]:
        if Path(origins[key]).resolve()!=(workspace/'tools/block'/name).resolve():raise ValueError('A compiler dependency has another origin.')

    # The compiler wrapper sits in tools beside the stock findlib and resource guard.
    runtime=deepcopy(config['proof_runtime'])
    if sealed:
        runtime['prepared_workspace']=str(workspace)
        launcher=list(runtime['mcp_argv'])
        receipts=[index for index,word in enumerate(launcher) if word=='--receipt']
        if len(receipts)!=1 or receipts[0]+1==len(launcher) or launcher[receipts[0]+1]!='{workspace}/STDIN-RELAY.json':
            raise ValueError('The sealed launcher lacks its exact relay output argument.')
        launcher[receipts[0]+1]=str(out/'STDIN-RELAY.json')
        runtime['mcp_argv']=launcher
    runtime['physical_compiler']=deepcopy(config['effective_compiler_version']['compiler'])
    runtime.update(harness=deepcopy(config.get('harness')),native_route=deepcopy(job.get('native_route')),control_session=deepcopy(config.get('control_session')),declaration_checks=deepcopy(config.get('declaration_checks',[])),
        phase=job['phase'],target={'block':job.get('target')},
        ordered_modules=job.get('ordered_modules',[]),job_output=str(out),
        canonical_admission=job['policy'])
    if job.get('native_route'):
        from minimal_prefix import delta_evidence
        runtime['native_delta']=delta_evidence(config,job['native_route'])
    runtime.pop('dependency_batch',None)
    from dependency_batch import for_phase as dependency_batch_for_phase
    dependency_spec=dependency_batch_for_phase(config,job['phase'])
    if dependency_spec:runtime['dependency_batch']=deepcopy(dependency_spec)
    runtime['coqc_wrapper']='tools/entry_chain_coqc.sh'
    runtime['prospective_directory']=str(out/'prospective')
    from rocq_mcp.server import _parse_project_flags
    expected=list(config['expected_mcp_flags'])
    actual=_parse_project_flags(workspace)
    if actual!=expected:raise ValueError('The pinned project parser returned another ordered flag vector.')
    runtime['expected_mcp_flags']=actual
    runtime['physical_flags']=[word.replace(str(source),str(workspace)) for word in config['physical_flags']]
    save(out/'PROJECT-PARSER.json',{'expected_flags':expected,'actual_flags':actual,'equal':True})
    from compiler_snapshot import declared_outputs
    declarations=declared_outputs(runtime['module_files'],runtime['ordered_modules'],workspace,config['bindings'],donor=source)
    runtime['declared_outputs']=declarations
    output_paths={name for row in declarations for name in row['outputs']}
    save(out/'DECLARED-OUTPUT-ABSENCE.json',{'modules':runtime['ordered_modules'],'declarations':declarations,
        'donor_bindings_preserved':True,'observed_before_snapshot':True})
    runtime['bindings']=list(config['bindings'])+[x['owned'] for x in copies
        if Path(x['owned']['path']).suffix in {'.v','.vo','.vos','.cmxs','.cma','.cmxa','.so'}
        and x['owned']['path'] not in output_paths]
    if runtime.get('native_delta'):
        evidence=runtime['native_delta']
        runtime['bindings'] += [evidence[k] for k in ['result','closure','release']]+[r['receipt'] for r in evidence['receipts']]
    # Record relocated project bytes separately from their original copy hashes.
    runtime['bindings'].extend(binding(workspace/name) for name in ['_CoqProject','_RocqProject'] if (workspace/name).is_file())
    runtime['bindings'].append(binding(workspace/'tools/resource_guard.sh'))
    runtime['bindings'].extend(binding(workspace/rel) for rel in config['guard_helper_paths'])
    runtime['bindings'].extend(binding(workspace/rel) for rel in [
        'tools/entry_chain_coqc.sh','tools/block/stock_scope_stdin_relay.py',
        'tools/block/entry_chain_compiler.py','tools/block/entry_chain.py',
        'tools/block/entry_chain_resources.py','tools/block/proof_bindings.py','tools/block/binding_cache.py','tools/block/compiler_snapshot.py','tools/block/seed_bindings.py','tools/block/runtime_ignores.py','tools/block/entry_chain_process.py','tools/block/entry_chain_plan.py'])
    if sealed or config.get('prepared_tool_transition'):
        runtime['bindings'].extend(row['owned'] for row in transition['copies'])
    # One canonical path can occur in source and physical views. Refuse differing hashes.
    unique={}
    for row in runtime['bindings']:
        if row['path'] in unique and unique[row['path']]['sha256']!=row['sha256']:
            raise ValueError('A runtime binding changed during final assembly.')
        unique[row['path']]=row
    runtime['bindings']=list(unique.values())
    for row in copies:
        if row['owned']['path']==str(workspace/'tools/block/entry_chain_resources.py'):
            row.update(source=binding(Path(__file__).with_name('entry_chain_resources.py')),owned=binding(workspace/'tools/block/entry_chain_resources.py'),scratch_policy_override=True)
    if config.get('seed_binding_reference'):
        from seed_bindings import compact
        if sealed:
            retained=deepcopy(config['seed_binding_reference'])
            deltas={row['relative']:row['sha256'] for row in retained['deltas']}
            for row in runtime['bindings']:
                path=Path(row['path'])
                if path.is_relative_to(workspace/'tools'):
                    deltas[path.relative_to(workspace).as_posix()]=row['sha256']
            retained['deltas']=[{'relative':name,'sha256':sha} for name,sha in sorted(deltas.items())]
            runtime['seed_binding_reference']=retained
        compact(runtime,config['seed_binding_reference']['descriptor'],workspace)
    from compiler_snapshot import externalize
    externalize(runtime,out/'BINDING-INVENTORY.json')
    save(out/'COPIES.json',copies);save(out/'RUNTIME.json',runtime)
    native=out/'native';native.mkdir()
    request={'runtime':str(out/'RUNTIME.json'),'runtime_sha256':digest(out/'RUNTIME.json'),
             'workspace':str(workspace),'output':str(native),'identity':config['identity']|{'block':job['key']}}
    save(native/'REQUEST.json',request)
    check_proof_bindings(runtime)
    return runtime,workspace


def final_accounting(group):
    stat=dict(line.split() for line in (group/'cpu.stat').read_text().splitlines())
    result={'cpu_seconds':int(stat['usage_usec'])/1e6,'raw_cpu_stat':stat,
        'scope':'Owned aggregate before final guard cleanup. Includes MCP/PET/compiler descendants.',
        'CPU_budget_enforced':False,'custom_observer':False}
    try:
        peak=int((group/'memory.peak').read_text())
        if peak<0:raise ValueError('The aggregate memory peak is negative.')
        result.update(aggregate_peak_bytes=peak,aggregate_peak_KiB=(peak+1023)//1024,
            memory_peak_source=str(group/'memory.peak'),final_memory_accounting_available=True)
    except (OSError,ValueError) as error:
        result.update(aggregate_peak_bytes=None,aggregate_peak_KiB=None,
            final_memory_accounting_available=False,memory_peak_error=str(error))
    try:
        result['memory_current_bytes']=int((group/'memory.current').read_text())
    except (OSError,ValueError) as error:
        result.update(memory_current_bytes=None,memory_current_error=str(error))
    from scratch_limits import memory_events
    result['memory_events']=memory_events(group)
    return result


def inside(out):
    normalize_cpu();out=Path(out)
    runtime=strict_loads((out/'RUNTIME.json').read_text())
    group=aggregate_root();info=group.stat()
    save(out/'BATCH-IDENTITY.json',{'aggregate_path':str(group),'aggregate_device':info.st_dev,
        'aggregate_inode':info.st_ino,'inside_pid':os.getpid(),'inside_startticks':ticks(os.getpid())})
    row=sample(Path('/proc')/str(os.getpid()),str(ticks(os.getpid())))
    from memory_policy import fence
    row['effective_limits']=effective(row['cgroup']);validate_limits(row,runtime['canonical_admission']['physical_fence_bytes'],memory_job=runtime['canonical_admission']['memory_job']);save(out/'CLIENT-LIMITS.json',row)
    check_operation(runtime)
    try:
        if (out/'KERNEL-ARGV.json').exists():
            command=strict_loads((out/'KERNEL-ARGV.json').read_text())
            kernel_environment=strict_loads((out/'KERNEL-ENVIRONMENT.json').read_text())
            kernel_environment['ZESU_AGGREGATE_SLICE']=os.environ['ZESU_AGGREGATE_SLICE']
            result=subprocess.run(command,cwd=Path(runtime['job_output'])/'workspace',env=kernel_environment)
        else:
            environment=None
            if runtime['phase']=='native':
                import stage1_runtime
                stage1_runtime.materialize_inside(out)
                environment=strict_loads((out/'prospective/ACTUAL-ENVIRONMENT.json').read_text())
            result=subprocess.run([sys.executable,'-B',str(Path(__file__).with_name('entry_chain_provider.py')),str(out/'native/REQUEST.json')],env=environment)

        return result.returncode
    finally:
        save(out/'CPU-FINAL.json',final_accounting(group))


def run_stock_job(config,job,out,prepared=None):
    from restart_bindings import verify_restart_runtime
    verify_restart_runtime(config,Path(__file__).resolve().parent.parent)
    from memory_policy import validate_job,environment,fence
    validate_job(job)
    normalize_cpu();out=Path(out)
    if prepared is None:out.mkdir(parents=True,exist_ok=False)
    self_cpu_start=resource.getrusage(resource.RUSAGE_SELF)
    token=prepared['owner']['token'] if prepared else uuid.uuid4().hex
    owner=prepared['owner'] if prepared else {'token':token,'pid':os.getpid(),'startticks':ticks(os.getpid()),'chain':config['identity'],'block':job['key']}
    key='EntryChain_'+job['key']+'_'+token
    policy=deepcopy(config['admission']);policy.update(claim_key=key,minimum_claim_bytes=job['claim_bytes'],physical_fence_bytes=job['physical_fence_bytes'],memory_job=job,capture_headroom_bytes=0,output_path=str(out),shared_latch=config['shared_latch'])
    job=dict(job,policy=policy)
    save(out/'STARTED.json',{'pid':os.getpid(),'startticks':ticks(os.getpid()),'owner':owner})
    reserved=False;child=None;child_start=None;result={};code=1
    try:
        if prepared:
            import collector
            collector.revalidate(read_bound(binding(out/'prospective/PHASE1.json')))
        reserve(policy,key,owner,out/'ADMISSION.json',recheck=lambda:binding_recheck(config));reserved=True
        if prepared:collector.revalidate(read_bound(binding(out/'prospective/PHASE1.json')))
        binding_recheck(config)
        runtime,workspace=(prepared['runtime'],prepared['workspace']) if prepared else stage_job(config,job,out)
        env=clean_environment();env.update(environment(job['phase'],job['claim_bytes'],job=job),PYTHONDONTWRITEBYTECODE='1',PYTHONHASHSEED='0')
        argv=outer_argv(workspace,job['key'],out)
        save(out/'LAUNCH.json',{'argv':argv,'owner':owner,'cpu_policy':'unlimited','custom_observer':False})
        with (out/'stock.stdout').open('wb') as stdout,(out/'stock.stderr').open('wb') as stderr:
            child=subprocess.Popen(argv,cwd=workspace,env=env,stdout=stdout,stderr=stderr,start_new_session=True)
            child_start=ticks(child.pid);save(out/'BATCH-PROCESS.json',{'pid':child.pid,'startticks':child_start});from scratch_limits import wait_with_limits
            code=wait_with_limits(child,out,job['claim_bytes'],0,phase=job['phase'],memory_job=job,family=(job.get('workload') or {}).get('kind') in {'stock_pass_spec_bundle','minimal_native_tactic'},family_threshold_bytes=(8 if (job.get('workload') or {}).get('kind')=='minimal_native_tactic' else 16)*1024**3)
        check_proof_bindings(runtime)
        receipts=read_optional(out/'native/NATIVE-RESULTS.json') or {}
        receipt=receipts.get('block',{})
        accepted=(code==0 and (out/'native/TRANSPORT-CLOSED.json').exists()) if job['phase']=='prerequisites' else (code==0 and receipt.get('compile_file_success') is True and receipt.get('verification_method')=='module_m' and receipt.get('assumptions')==[])
        result={'schema':'entry-chain.block-result.v1','block':job['key'],'success':accepted,'returncode':code,'phase':job['phase'],'native_receipts':receipts,'proof_accepted_by_Root':False}
    except BaseException as error:
        result={'schema':'entry-chain.block-result.v1','block':job['key'],'success':False,'error':str(error),'traceback':traceback.format_exc(),'proof_accepted_by_Root':False}
        save(out/'CONTROLLER-FAILURE.json',result)
        if child is not None and child.poll() is None:child.wait()
    finally:
        if reserved:
            batch=read_optional(out/'BATCH-IDENTITY.json');client=read_optional(out/'CLIENT-LIMITS.json');checks=[]
            if child is not None:checks.append({'pid':child.pid,'startticks':child_start,'ended':not identity_alive(child.pid,child_start)})
            if batch:
                checks.append({'pid':batch['inside_pid'],'startticks':batch['inside_startticks'],'ended':not identity_alive(batch['inside_pid'],batch['inside_startticks'])})
                ended=all(row['ended'] for row in checks) and closed_aggregate(batch,child.pid,child_start)
            else:ended=all(row['ended'] for row in checks)
            closure={'owner':owner,'all_owned_actors_closed':ended,'actors':checks,'batch_identity':batch,'claim_key':key,'closure_basis':'Batch process ended and exact owned aggregate is empty or absent.','aggregate_actor_telemetry':'unavailable under scratch policy'}
            save(out/'CLOSURE.json',closure)
            if ended:save(out/'RELEASE.json',release(policy,key,owner,binding(out/'CLOSURE.json')))
            else:result.update(success=False,closure_pending=True)
        self_cpu_end=resource.getrusage(resource.RUSAGE_SELF)
        result.update(module=(job.get('target') or {}).get('module'),statement_sha256=(job.get('target') or {}).get('statement_sha256'),native_receipts=read_optional(out/'native/NATIVE-RESULTS.json') or {},CPU=read_optional(out/'CPU-FINAL.json'),aggregate_peak_KiB=None,aggregate_telemetry_available=False,observer_failure=None,custom_observer=False,controller_self_CPU_seconds=self_cpu_end.ru_utime+self_cpu_end.ru_stime-self_cpu_start.ru_utime-self_cpu_start.ru_stime,controller_CPU_scope='Controller only. No custom observer runs.')
        result['memory_growth']=read_optional(out/'MEMORY-GROWTH.json')
        accounting=result['CPU'] or {}
        result.update(aggregate_peak_KiB=accounting.get('aggregate_peak_KiB'),
            aggregate_peak_bytes=accounting.get('aggregate_peak_bytes'),
            final_memory_accounting_available=accounting.get('final_memory_accounting_available',False))
        try:
            result.update(entry_chain_result.summarize(out,job,result))
            if result.get('shared_infrastructure_failure'):publish_latch(config['shared_latch'],'shared-infrastructure-failure',{'job':job['key'],'result':result})
        except BaseException as error:
            result.update(success=False,status='infrastructure_failed',summary_error=repr(error),shared_infrastructure_failure=True);publish_latch(config['shared_latch'],'result-summary-failed',{'job':job['key'],'error':repr(error)})
        save(out/'RESULT.json',result)
    return 0 if result.get('success') is True else 1


def run_job(config,job,out):
    if job['phase']=='native':
        import stage1_runtime
        try:
            return stage1_runtime.run_native(config,job,out,sys.modules[__name__])
        except BaseException as error:
            output=Path(out);output.mkdir(parents=True,exist_ok=True)
            failure={'success':False,'block':job['key'],'status':'infrastructure_failed','last_phase':'cache_or_prospective_collection','group_counts':None,'error':str(error),'traceback':traceback.format_exc(),'shared_infrastructure_failure':True}
            save(output/'CACHE-OR-COLLECTION-FAILURE.json',failure)
            if not (output/'RESULT.json').exists():save(output/'RESULT.json',failure)
            publish_latch(config['shared_latch'],'cache-or-prospective-collection-failed',failure)
            return 1
        finally:
            output=Path(out)
            if (output/'RESULT.json').exists():save(output/'DISPATCH-FINISHED.json',{'result':binding(output/'RESULT.json'),'time_ns':time.time_ns(),'cache_processing_finished':True})
    return run_stock_job(config,job,out)

def read_optional(path):
    return strict_loads(path.read_text()) if Path(path).is_file() else None


def main():
    if sys.argv[1:2]==['--inside']:return inside(sys.argv[2])
    config_path,expected,key,out=sys.argv[1:]
    if Path(out).is_dir():save(Path(out)/'CONTROLLER-START.json',{'time_ns':time.time_ns(),'monotonic_ns':time.monotonic_ns(),'pid':os.getpid(),'startticks':ticks(os.getpid())})
    config=read_bound({'path':config_path,'sha256':expected})
    if not config.get('execution_released'):raise ValueError('The chain runtime is not released.')
    job=next(x for x in config['jobs'] if x['key']==key)
    return run_job(config,job,out)


if __name__=='__main__':raise SystemExit(main())
