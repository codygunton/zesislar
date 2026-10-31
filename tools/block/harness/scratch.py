#!/usr/bin/env python3
"""Prepare and run an exact block target with the shared commit-pinned harness."""
from pathlib import Path
from copy import deepcopy
import argparse,hashlib,json,os,re,shlex,shutil,subprocess,sys,time,uuid
HERE=Path(__file__).resolve().parent
sys.dont_write_bytecode=True
if __name__=='__main__':
    from command_scope import enter
    enter(__file__,sys.argv[1:])
W=HERE.parents[2]
os.environ['PATH']='/home/cody/islaris/_opam/bin:/home/cody/.local/bin:/usr/local/bin:/usr/bin:/bin'
os.environ['OPAM_SWITCH_PREFIX']='/home/cody/islaris/_opam'
os.environ['PYTHONDONTWRITEBYTECODE']='1'
sys.dont_write_bytecode=True
sys.path[:0]=[str(HERE/'code'),str(HERE),str(W/'tools/block'),str(W/'tools')]
import clone_copy
from runtime_ignores import excluded as excluded_runtime_file,python_argv
from entry_chain import binding,check_bindings,digest,read_bound,save,strict_loads
from entry_chain_run import check_project_paths
from entry_chain_stage import invalidation,import_commands
from scratch_statement import source_statement
from proof_bindings import proof_rows,coordination_rows,check_proof_bindings
from installed_mappings import InstalledMappings
def _parse_project_flags(workspace):
    from rocq_mcp.server import _parse_project_flags as parse
    return parse(workspace)
ENTRY='ZesuSsz.Generated.DecodeItem.Entries'
RULES='ZesuSsz.Evidence.RuleScratchRules'
PYTHON=Path('/home/cody/.local/share/uv/tools/rocq-mcp/bin/python')

def arguments(argv):
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--harness-commit',required=True);p.add_argument('--supplier-controls',type=Path);p.add_argument('--dependency-batch',type=Path);p.add_argument('--seed-reference',type=Path);p.add_argument('--dependency-cache',type=Path);p.add_argument('--end-cleanup',choices=['on','off'],default='on',help='Use off for reusable prefixes, seeds, and queued inputs.');p.add_argument('--admission-profile',type=Path);p.add_argument('--completed-stock-measurements',type=Path);p.add_argument('--cache',choices=['off','on'],default='off');p.add_argument('block');p.add_argument('entry_file',type=Path);p.add_argument('--rules',type=Path);p.add_argument('--output',type=Path);p.add_argument('--prepare-only',action='store_true');p.add_argument('--source-overrides',type=Path);p.add_argument('--declarations-only',action='store_true');p.add_argument('--target-adapter',type=Path);p.add_argument('--sizing',type=Path);p.add_argument('--base-runtime',type=Path);p.add_argument('--base-runtime-sha256');p.add_argument('--normalization-policy',type=Path);p.add_argument('--prerequisite-target-union',action='store_true');p.add_argument('--declaration-checks',type=Path);p.add_argument('--control-session',type=Path)
    a=p.parse_args(argv);a.block=a.block.lower().removeprefix('0x')
    if not a.target_adapter:p.error('The shared harness requires a target adapter.')
    if not a.base_runtime:p.error('The shared harness requires an exact base runtime.')
    rows=[]
    if a.target_adapter:
        adapter=read_bound(binding(a.target_adapter));rows=read_bound(adapter['targets'])['rows']
    if a.cache=='on' and (a.declarations_only or a.control_session):p.error('Cache reuse requires a native checkpoint.')
    if a.dependency_batch and (not a.declarations_only or not a.prerequisite_target_union or a.control_session):p.error('Dependency waves require a declaration-only target union.')
    if a.control_session and (not a.declarations_only or not a.rules or a.declaration_checks):p.error('A control session requires rules and declarations-only mode without exact declaration checks.')
    if a.prerequisite_target_union and (not a.target_adapter or not a.declarations_only):p.error('A prerequisite union requires a target adapter and declarations-only mode.')
    if a.base_runtime and (not a.base_runtime_sha256 or len(a.base_runtime_sha256)!=64):p.error('A base runtime requires its exact SHA256.')
    if a.block not in {r.get('key',format(r['pc'],'x')).lower() for r in rows}:p.error('The block is outside the bound target set.')
    for f in [a.entry_file,a.rules]:
        if f is not None and (not f.is_file() or f.suffix!='.v'):p.error('Every entry or rules input must be an existing .v file.')
    if a.output is None:a.output=W/'_build/rule-scratch-attempts'/uuid.uuid4().hex
    a.output=a.output.resolve()
    if a.output.exists():p.error('The output already exists. The harness never overwrites a result.')
    base=Path('/home/cody/zesislar')
    if a.output.is_relative_to(base):
        rel=a.output.relative_to(base).parts
        private=bool(rel and rel[0]=='_build') or bool(len(rel)>2 and rel[0]=='.worktrees' and rel[2]=='_build')
        if not private:p.error('The output must be private build data or outside every source tree.')
    return a

def strict_bindings(rows):
    seen=set()
    for row in rows:
        path=str(Path(row['path']).resolve())
        if path in seen:raise ValueError('The runtime repeats a binding: '+path)
        seen.add(path)
    check_bindings(rows)

def combined_bindings(rows):
    result={}
    for row in rows:
        if excluded_runtime_file(row['path']):continue
        path=str(Path(row['path']).resolve())
        if path in result and result[path]['sha256']!=row['sha256']:raise ValueError('Conflicting source bindings: '+path)
        result[path]={'path':path,'sha256':row['sha256']}
    strict_bindings(list(result.values()));return list(result.values())

def canonical_edges(module,text,old_text,edges,module_files,installed=None,source_path=None):
    if installed is not None:installed.register_source(text,source_path)
    if installed is None and old_text is not None and import_commands(text)==import_commands(old_text):return [r for r in edges if r['from']==module]
    result=[]
    for words,names in import_commands(text):
        # Import/Export opens a namespace. Only Require loads a library.
        if 'Require' not in words:continue
        for name in names:
            if name not in module_files:
                if installed is None:raise ValueError('An import has no exact canonical mapping: '+name)
                installed.resolve(name)
                name=installed.resolutions[name]['canonical']
            row={'from':module,'to':name}
            if row not in result:result.append(row)
    return result

def reconcile_import_closure(targets,edges,module_files,workspace,installed):
    """Read every bound source header in the complete requested closure."""
    result=list(edges);seen=set();pending=list(targets)
    while pending:
        module=pending.pop()
        if module in seen:continue
        seen.add(module)
        if module not in module_files:continue
        path=Path(workspace)/module_files[module]
        if not path.is_file():raise ValueError('A closure source is absent: '+module)
        current=canonical_edges(module,path.read_text(),None,result,module_files,installed,path)
        result=[row for row in result if row['from']!=module]+current
        pending.extend(row['to'] for row in current)
    return result

def missing_prerequisite_objects(targets,forward,modules,workspace):
    from entry_chain_stage import graph_closure
    return [name for name in graph_closure(targets,forward)
            if name in modules and not (workspace/modules[name]).with_suffix('.vo').is_file()]

def relative_projects(workspace,old_workspace):
    for name in ['_CoqProject','_RocqProject']:
        path=workspace/name;rows=[]
        path.chmod(path.stat().st_mode|0o200)
        for line in path.read_text().splitlines():
            words=shlex.split(line,comments=True)
            if not words:continue
            if words[0] not in {'-Q','-R','-I'}:raise ValueError('Unsupported project directive.')
            physical=Path(words[1])
            if physical.is_absolute() and physical.is_relative_to(old_workspace):words[1]=str(physical.relative_to(old_workspace))
            rows.append(shlex.join(words))
        path.write_text('\n'.join(rows)+'\n')
    check_project_paths(workspace)

def configure_cache(runtime,setting):
    if setting not in {'off','on'}:raise ValueError('The cache setting is unsupported.')
    runtime['result_cache']=dict(runtime['result_cache'],purpose='exploration' if setting=='on' else 'confirmation')
    runtime['cache_policy']=dict(runtime.get('cache_policy',{}),enabled=setting=='on')

def runtime_cache_setting(runtime):
    purpose=runtime.get('result_cache',{}).get('purpose','confirmation')
    if purpose not in {'exploration','confirmation','gate','merge'}:raise ValueError('The cache purpose is unsupported.')
    return 'on' if purpose=='exploration' else 'off'

def summarize(result,job_output,cache_setting='off'):
    status=result.get('status')
    if status in {'passed','native_open'}:
        import result_cache
        result_cache.validate_result(result)
    value={'status':'closed' if status=='passed' else 'open' if status=='native_open' else 'infrastructure_failed','success':status=='passed','group_counts':result.get('group_counts'),'complete_state':result.get('complete_state'),'CPU':result.get('CPU'),'aggregate_peak_bytes':result.get('aggregate_peak_bytes'),'native_result':binding(Path(job_output)/'RESULT.json'),'source_statement_sha256':result.get('statement_sha256'),'cache':'on; exploration checkpoint' if cache_setting=='on' else 'off; confirmation rule test','cache_status':result.get('cache_status')}
    if value['status']=='infrastructure_failed':
        value.update(first_error=result.get('error',result.get('summary_error')),last_phase=result.get('last_phase'),private_errors=result.get('private_errors',[]))
    if value['status']=='open':
        state=value['complete_state']
        if not state or state['state_source'] not in {'successful_command_returned_state','returned_error_state'}:raise ValueError('An open verdict lacks a returned residual.')
        read_bound(state)
    if (Path(job_output)/'EXTERNAL-STOP.json').exists():
        value.update(status='resource_stopped',success=False,external_stop=binding(Path(job_output)/'EXTERNAL-STOP.json'))
    return value

def full_fence_attempt(attempt):
    """Bind the single-proof fence and its shared ancestor into the cache key."""
    attempt=deepcopy(attempt)
    attempt['limits'].update(memory_bytes=64*1024**3,swap_bytes=0)
    scopes=[row for row in attempt['scope_limits'] if row['role']!='workloads']
    for row in scopes:
        if row['role'] in {'aggregate','batch','client','mcp','pet','compiler'}:row.update(memory_bytes=64*1024**3,swap_bytes=0)
        if row['role']=='aggregate':row['parent']='workloads'
    scopes.append({'role':'workloads','parent':None,'memory_bytes':175*1024**3,
                   'swap_bytes':0,'cpu_seconds':None,'wall_seconds':None})
    attempt['scope_limits']=scopes
    return attempt


def prestage_sealed(c,out):
    """Complete nonproof staging once before freezing the one native config."""
    if not c.get('seed_binding_reference') or c.get('declarations_only'):return
    from seed_bindings import descriptor
    if not descriptor(c['seed_binding_reference']['descriptor']).get('sealed_boundary'):return
    pre,job=c['jobs']
    if pre['ordered_modules']:raise ValueError('A sealed native requires a completed setup prefix.')
    if c.get('declaration_checks') or c.get('control_session'):raise ValueError('A sealed native cannot contain controls.')
    started=time.monotonic()
    save(out/'READINESS.json',{'schema':'entry-chain.prerequisite-readiness.v1','objects':[],
        'existing_compatible_objects':True,'no_compilation_repeated':True})
    c['readiness']=binding(out/'READINESS.json')
    c['bindings']=combined_bindings(c['bindings']+[c['readiness']])
    import entry_chain_run,stage1_runtime
    output=Path(job['output']);output.mkdir(parents=True,exist_ok=False)
    runtime,workspace=entry_chain_run.stage_job(c,dict(job,policy={'minimum_claim_bytes':job['claim_bytes'],'physical_fence_bytes':job['physical_fence_bytes'],'memory_job':job}),output)
    stage1_runtime.prepare(c,job,output,runtime,workspace)
    c['seed_binding_reference']=deepcopy(runtime['seed_binding_reference'])
    c['sealed_native_preparation']={'job':job['key'],'output':str(output),
        'runtime':binding(output/'RUNTIME.json'),'phase1':binding(output/'prospective/PHASE1.json'),
        'key':binding(output/'prospective/KEY.json')}
    c['bindings']=combined_bindings(c['bindings']+[c['sealed_native_preparation'][name] for name in ['runtime','phase1','key']])
    save(out/'SEALED-PREPARATION.json',{'elapsed_seconds':time.monotonic()-started,
        'work_in_preparation':'Tool installation, typed collection, Python resolution, and key construction.',
        'claims_created':0,'proof_calls':0,'native_config_copies':1,'workspace_copies':1})


def sealed_rules_prefix(profile_binding,declarations_only,control_session):
    """Keep focused controls separate from exact native-prefix adoption."""
    from native_route import for_profile,authority
    from minimal_prefix import common
    profile=read_bound(profile_binding)
    from memory_policy import PORT_KIND,production_port_authority
    if profile.get('kind')==PORT_KIND:
        production_port_authority(profile)
        if declarations_only or control_session:raise ValueError('The production PORT profile requires ordinary stock native execution.')
        return None
    if profile.get('kind')=='focused_check':
        if not declarations_only:raise ValueError('A focused profile requires declaration-only execution.')
        return None
    route=for_profile(profile_binding)
    if not route:raise ValueError('The sealed profile lacks an exact native authority or focused classification.')
    if control_session:raise ValueError('A native authority cannot classify an interactive control.')
    selected=authority(route)['common_prefix']
    return selected,common(selected)


def prepare(a):
    from command_scope import require
    require()
    from harness_commit import pin
    harness=pin(a.harness_commit)
    out=a.output;out.mkdir(parents=True,exist_ok=False)
    baseline={'path':str(a.base_runtime),'sha256':a.base_runtime_sha256}
    c=read_bound(baseline)
    c['harness']=harness
    from supplier_release import releases
    c['supplier_releases']=releases(read_bound(binding(a.supplier_controls))) if a.supplier_controls else []
    save(out/'HARNESS.json',harness)
    from dependency_batch import inherit as inherit_dependency_batch
    wave_transition=inherit_dependency_batch(c)
    if wave_transition['removed'] or wave_transition['removed_nested']:
        save(out/'DECLARATION-WAVE-TRANSITION.json',dict(wave_transition,source_runtime=baseline,lineage_retained=True))
    if a.seed_reference:
        from seed_bindings import compact
        compact(c,binding(a.seed_reference.resolve()),c['prepared_workspace'])
    old=deepcopy(c);coordination=coordination_rows(c);c['bindings']=proof_rows(c);check_proof_bindings(c);c['coordination_bindings']=coordination;c['watcher']=binding(Path('/home/cody/ai-workflow/ai-coord/ai-coord.py'))
    if a.dependency_cache:c['dependency_resolution_cache']=binding(a.dependency_cache.resolve())
    source=Path(c['prepared_workspace']);workspace=out/'prepared'
    sealed=False
    if c.get('seed_binding_reference'):
        from seed_bindings import descriptor,clone_owned
        sealed=bool(descriptor(c['seed_binding_reference']['descriptor']).get('sealed_boundary'))
    if sealed:clone_owned(c['seed_binding_reference']['descriptor'],workspace)
    else:clone_copy.copytree(source,workspace,symlinks=True)
    for link in workspace.rglob('*'):
        if link.is_symlink() and not link.resolve().is_relative_to(workspace):raise ValueError('A copied import alias leaves the owned workspace.')
    relative_projects(workspace,source)
    from restart_bindings import install_restart_tools
    recovery=install_restart_tools(workspace,c,HERE);save(out/"RECOVERY-TOOLS.json",recovery)
    if sealed and a.admission_profile:
        selected=sealed_rules_prefix(binding(a.admission_profile),a.declarations_only,a.control_session)
        if selected:
            prefix_binding,prefix=selected
            rule=next(row for row in prefix['modules'] if row['module']==RULES)
            destination=workspace/c['proof_runtime']['module_files'][RULES]
            clone_copy.copy2(rule['source']['path'],destination);clone_copy.copy2(rule['object']['path'],destination.with_suffix('.vo'))
            save(out/'COMPILED-RULES-INSTALL.json',{'prefix':prefix_binding,'source':rule['source'],
                'object':rule['object'],'installed_source':binding(destination),'installed_object':binding(destination.with_suffix('.vo')),
                'compiler_calls':0,'method':'FICLONE from the completed source-bound prefix'})
    modules=c['proof_runtime']['module_files'];graph=read_bound(c['cache_import_graph']);adapter=None
    if a.target_adapter:
        adapter=read_bound(binding(a.target_adapter));graph=read_bound(adapter['graph']);modules.update(graph['module_files'])
    edges=graph['import_edges'];changed=[];changes=[]
    installed=InstalledMappings([word.replace(str(source),str(workspace)) for word in c['physical_flags']],receipt_dir=out/'IMPORT-RESOLUTION')
    entry=workspace/modules[ENTRY];before=entry.read_text();entry_text=a.entry_file.read_text()
    if entry_text!=before:
        edges=[r for r in edges if r['from']!=ENTRY]+canonical_edges(ENTRY,entry_text,before,edges,modules,installed,a.entry_file)
        clone_copy.copy2(a.entry_file,entry);changed.append(ENTRY)
    overrides=(read_bound(adapter['overrides']) if adapter else [])+(strict_loads(a.source_overrides.read_text()) if a.source_overrides else [])
    if not isinstance(overrides,list):raise ValueError('Source overrides must be a list.')
    seen=set()
    for override in overrides:
        if set(override)!={'module','path','sha256'}:raise ValueError('A source override has unknown fields.')
        name=override['module']
        if name in seen or name not in modules:raise ValueError('A source override repeats or names an unknown module.')
        seen.add(name);incoming=Path(override['path']);check_bindings([{'path':str(incoming),'sha256':override['sha256']}])
        target_path=workspace/modules[name];target_path.parent.mkdir(parents=True,exist_ok=True);original=target_path.read_text() if target_path.exists() else None;replacement=incoming.read_text()
        edges=[r for r in edges if r['from']!=name]+canonical_edges(name,replacement,original,edges,modules,installed,incoming)
        content_changed=not target_path.exists() or target_path.read_bytes()!=incoming.read_bytes()
        clone_copy.copy2(incoming,target_path)
        if content_changed:changed.append(name)
    for released in c['supplier_releases']:
        name=released['module']
        if name not in modules or digest(workspace/modules[name])!=released['source']['sha256']:
            raise ValueError('The released supplier differs from its staged source.')
    targets=read_bound(adapter['targets'])['rows'];target=next(r for r in targets if r.get('key',format(r['pc'],'x')).lower()==a.block);module=target['module'];native=workspace/modules[module]
    from native_route import for_profile,source_body,authority,input_bindings
    native_route=for_profile(binding(a.admission_profile)) if a.admission_profile else None
    native_body=source_body(binding(a.admission_profile)) if a.admission_profile else 'zesu_block.'
    expected_statement=source_statement(native,native_body)['statement'];assert hashlib.sha256(expected_statement.encode()).hexdigest()==target['statement_sha256']
    if a.rules:
        rule_path=workspace/'artifacts/default/ZesuSsz/Evidence/RuleScratchRules.v';rule_path.parent.mkdir(parents=True,exist_ok=True);incoming_rules=a.rules.read_bytes();previous_rules=rule_path.read_bytes() if rule_path.exists() else None;clone_copy.copy2(a.rules,rule_path);modules[RULES]=str(rule_path.relative_to(workspace))
        if previous_rules!=incoming_rules:changed.append(RULES)
        edges+=canonical_edges(RULES,rule_path.read_text(),None,edges,modules,installed,a.rules)
        edges.append({'from':module,'to':RULES})
    if a.rules or native_route:
        from scratch_imports import install_rules_import
        save(out/'SCRATCH-IMPORT.json',install_rules_import(native,RULES,lambda path:source_statement(path,native_body),native_route))
    assert source_statement(native,native_body)['statement']==expected_statement
    plan_targets=[row['module'] for row in targets] if a.prerequisite_target_union else ([RULES] if a.declarations_only and a.rules else [module])
    closure_targets=list(dict.fromkeys([row['module'] for row in targets]+[name for name in modules if '.Generated.' in name]+plan_targets))
    edges=reconcile_import_closure(closure_targets,edges,modules,workspace,installed)
    forward={}
    for edge in edges:forward.setdefault(edge['from'],set()).add(edge['to'])
    missing=missing_prerequisite_objects(closure_targets,forward,modules,workspace)
    changed=list(set(changed)|set(missing))
    plan=invalidation(edges,changed,plan_targets)
    native_targets={row['module'] for row in targets}
    plan['prerequisites']=[name for name in plan['ordered_required'] if name not in native_targets]
    plan['native_targets']=[name for name in plan['ordered_required'] if name in native_targets]
    if a.declarations_only and not a.prerequisite_target_union and a.rules:plan['prerequisites']=plan['ordered_required']
    if a.control_session:plan['prerequisites']=[name for name in plan['prerequisites'] if name!=RULES]
    plan['import_edges']=edges;plan['proof_ran']=False
    # Never retain an old native object. Also remove every changed dependent object.
    for name in set(plan['invalidated_modules'])|{module}:
        if name not in modules:continue
        stem=workspace/modules[name]
        for ext in ['.vo','.vos','.vok','.glob','.aux']:
            q=stem.with_suffix(ext)
            if q.exists():q.unlink()
    save(out/'INVALIDATION.json',plan)
    sizing={'claim_bytes':64*1024**3,'basis':'unmeasured_full_fence'}
    if a.sizing:
        candidates=read_bound(binding(a.sizing))['rows'];measurement=next(r for r in candidates if r['key'].lower()==a.block)
        if measurement['claim_proposal_bytes']!=(3*measurement['peak_prediction_bytes']+1)//2:raise ValueError('The matrix claim differs from its measured prediction.')
        check_bindings([v for observation in measurement['observations'] for v in observation.values() if isinstance(v,dict) and set(v)>={'path','sha256'}])
        sizing=dict(measurement,claim_bytes=measurement['claim_proposal_bytes'])
    native_job={'key':a.block,'phase':'native','claim_bytes':64*1024**3,'target':{'module':module,'pc':target['pc'],'source_sha256':digest(native),'statement_sha256':target['statement_sha256']},'output':str(out/'jobs'/a.block)}
    if native_route:
        native_job.update(native_route=native_route,ordered_modules=[])
        c['native_route']=native_route
    else:c.pop('native_route',None)
    pre={'key':'prerequisites','phase':'prerequisites','claim_bytes':64*1024**3,'ordered_modules':plan['prerequisites'],'output':str(out/'jobs/prerequisites')}
    if a.declarations_only:pre['target']=deepcopy(native_job['target'])
    from memory_policy import apply_job
    completed_rows=read_bound(binding(a.completed_stock_measurements))['rows'] if a.completed_stock_measurements else []
    native_job=apply_job(native_job,completed_rows);pre=apply_job(pre)
    if a.admission_profile:
        from memory_policy import workload_for_job
        context=binding(a.admission_profile)
        actual_config=dict(c,prepared_workspace=str(workspace),proof_runtime=dict(c['proof_runtime'],module_files=modules),declarations_only=a.declarations_only,prerequisite_modules=pre['ordered_modules'])
        native_job=apply_job(native_job,completed_rows,workload_for_job(context,native_job,actual_config))
        pre=apply_job(pre,workload=workload_for_job(context,pre,actual_config))
        c['admission_profile']=context
    if a.normalization_policy:
        policy=read_bound(binding(a.normalization_policy))
        if set(policy)!={'hook_enabled','database','registrations'} or not isinstance(policy['hook_enabled'],bool) or policy['database']!='zesu_entry_normalize':raise ValueError('The normalization policy is invalid.')
        check_bindings(policy['registrations'])
        if a.rules is None and policy['registrations']:raise ValueError('A registered policy has no rules module.')
        if a.rules is not None and binding(a.rules) not in policy['registrations']:raise ValueError('The policy omits its rules module.')
    else:policy=None
    if adapter and policy is None:raise ValueError('A production matrix requires its explicit database policy.')
    c['declaration_checks']=read_bound(binding(a.declaration_checks)) if a.declaration_checks else []
    for check in c['declaration_checks']:
        if set(check)!={'problem_name','problem_statement','proof'} or not all(isinstance(v,str) and v for v in check.values()):raise ValueError('A declaration check has invalid fields.')
    if c['declaration_checks'] and not a.declarations_only:raise ValueError('Declaration checks require declaration-only mode.')
    c['entry_normalization_policy']=policy
    c['control_session']=read_bound(binding(a.control_session)) if a.control_session else None
    c['declarations_only']=a.declarations_only
    c['source_overrides']=overrides
    c.update(jobs=[pre,native_job],selected_blocks=[a.block],prepared_workspace=str(workspace),runtime_path=str(out/'RUNTIME.json'),shared_latch=str(out/'INFRASTRUCTURE-HOLD.json'),readiness={'path':str(out/'READINESS.json'),'sha256':None},execution_released=True,priority_claim=None,job_controller=binding(HERE/'code/entry_chain_run.py'),scratch_provider=binding(HERE/'code/entry_chain_provider.py'),result_adapter=binding(HERE/'code/entry_chain_result.py'),cache_import_graph=binding(out/'INVALIDATION.json'),reuse_prerequisites=False,variant='one-block-rule-scratch')
    from native_route import validate_prerequisite_order
    validate_prerequisite_order(c)
    c['cache_attempt']['limits'].update(cpu_seconds=7200,memory_bytes=68719476736)
    from port_native_policy import configure_cpu
    search_budget,setup_budget=configure_cpu(c,native_job)
    c['memory_claim_report_multiplier']=2
    c['cache_attempt']=full_fence_attempt(c['cache_attempt'])
    configure_cache(c,a.cache);c['physical_flags']=[x.replace(str(source),str(workspace)) for x in c['physical_flags']];c['expected_mcp_flags']=_parse_project_flags(workspace)
    c['identity']=dict(c['identity'],rule_scratch={'block':a.block,'entry':binding(a.entry_file),'rules':binding(a.rules) if a.rules else None,'statement_sha256':target['statement_sha256']})
    if getattr(a,'dependency_batch',None):
        from dependency_batch import attach
        wave_plan=attach(c,binding(a.dependency_batch))
    else:wave_plan=None
    implementations=[binding(out/'HARNESS.json')]
    c['cache_producer_files']={'implementation':[dict(r,id='scratch-implementation:'+str(i),kind='source') for i,r in enumerate(implementations)],'inputs':[dict(binding(a.entry_file),id='scratch-entry',kind='source')]+([dict(binding(a.declaration_checks),id='declaration-checks',kind='configuration')] if a.declaration_checks else [])+([dict(binding(a.normalization_policy),id='entry-normalization-policy',kind='configuration')] if a.normalization_policy else [])+([dict(binding(a.rules),id='scratch-rules',kind='source')] if a.rules else []),'outputs':[dict(binding(native),id='scratch-native',kind='source'),dict(binding(entry),id='scratch-entries',kind='source')]}
    if a.supplier_controls:c['cache_producer_files']['inputs'].append(dict(binding(a.supplier_controls),id='supplier-activation-controls',kind='configuration'))
    if a.admission_profile:c['cache_producer_files']['inputs'].append(dict(binding(a.admission_profile),id='admission-profile',kind='configuration'))
    additions=([binding(a.supplier_controls)] if a.supplier_controls else [])+([binding(a.admission_profile)] if a.admission_profile else [])+([binding(a.control_session)] if a.control_session else [])+([binding(a.declaration_checks)] if a.declaration_checks else [])+([binding(a.normalization_policy)] if a.normalization_policy else [])+([binding(a.target_adapter),adapter['targets'],adapter['overrides'],adapter['graph']] if adapter else [])+([binding(a.sizing)] if a.sizing else [])+[{'path':r['path'],'sha256':r['sha256']} for r in overrides]+([binding(a.source_overrides)] if a.source_overrides else [])+implementations+[binding(installed.coqdep),binding(a.entry_file),binding(out/'INVALIDATION.json')]+([binding(a.rules)] if a.rules else [])
    if wave_plan:
        wave_inputs=[binding(a.dependency_batch),wave_plan['source_boundary']]+[wave_plan[key] for key in ['guard','compile_measure_helper','run_registry','compiler','dune']]+[row['source'] for row in wave_plan['modules']]
        additions+=wave_inputs
        c['cache_producer_files']['inputs']+=[dict(row,id='declaration-wave:'+str(i),kind='configuration') for i,row in enumerate(wave_inputs)]
    if (out/'DECLARATION-WAVE-TRANSITION.json').exists():additions.append(binding(out/'DECLARATION-WAVE-TRANSITION.json'))
    if a.completed_stock_measurements:
        additions.append(binding(a.completed_stock_measurements))
        for memory_job in [pre,native_job]:
            basis=memory_job.get('completed_stock_measurement')
            if basis:
                evidence=basis['measurement']
                names=['native_source','result','acceptance','release_ledger','compiler'] if evidence.get('format')=='legacy_r1_workload_rss_v1' else ['native_source','result','closure','release']
                additions.extend(evidence[name] for name in names)
                if evidence.get('declaration_projection'):
                    projection=read_bound(evidence['declaration_projection']);additions.extend([evidence['declaration_projection']]+[projection[name] for name in ['current_source','legacy_interval','declaration']])
                if evidence.get('format')=='completed_stock_verification_repair_v1':
                    from memory_policy import verification_bindings
                    additions.extend(verification_bindings(evidence))
                elif evidence.get('format')!='legacy_r1_workload_rss_v1':additions.append(read_bound(evidence['result'])['complete_state'])
    if c.get('dependency_resolution_cache'):
        cached=c['dependency_resolution_cache'];read_bound(cached);additions.append(cached)
        c['cache_producer_files']['inputs'].append(dict(cached,id='dependency-resolution-cache',kind='configuration'))
    from memory_policy import profile_bindings,PORT_KIND
    measured_inputs=profile_bindings(binding(a.admission_profile) if a.admission_profile else None)
    additions += measured_inputs
    c['cache_producer_files']['inputs'] += [dict(row,id='memory-evidence:'+str(i),kind='configuration') for i,row in enumerate(measured_inputs)]
    additions += input_bindings(native_route)
    if native_route:
        c['cache_producer_files']['inputs'].append(dict(native_route,id='minimal-native-authority',kind='configuration'))
    additions += [row['owned'] for row in recovery['copies']]+[binding(out/'RECOVERY-TOOLS.json')]
    if sealed:
        additions += [binding(native),binding(entry)]+[binding(workspace/modules[row['module']]) for row in overrides]
        if not a.admission_profile or read_bound(binding(a.admission_profile)).get('kind')!=PORT_KIND:
            additions.append(binding(workspace/modules[RULES]))
            rule_object=(workspace/modules[RULES]).with_suffix('.vo')
            if rule_object.is_file():additions.append(binding(rule_object))
    else:additions += [binding(p) for p in workspace.rglob('*') if p.is_file() and not p.is_symlink() and p.suffix in {'.v','.vo','.cmxs'}]
    additions += [binding(workspace/name) for name in ['_CoqProject','_RocqProject']]
    c['proof_runtime']['mcp_argv']=python_argv(c['proof_runtime']['mcp_argv'])
    c['adoption_implementation']=binding(HERE/'code/full_chain.py')
    c['bindings']=combined_bindings(c['bindings']+additions+[c['adoption_implementation']])
    if c.get('seed_binding_reference'):
        from seed_bindings import compact
        compact(c,c['seed_binding_reference']['descriptor'],c['prepared_workspace'])
        check_proof_bindings(c)
    if digest(entry)!=digest(a.entry_file):raise ValueError('The entry input changed during preparation.')
    if a.rules and digest(workspace/modules[RULES])!=digest(a.rules):raise ValueError('The rules input changed during preparation.')
    from end_run_cleanup import policy as cleanup_policy
    c['end_of_run_cleanup']=cleanup_policy(a.end_cleanup=='on')
    check_declaration_target(c)
    save(out/'INPUTS.json',{'end_of_run_cleanup':c['end_of_run_cleanup'],'block':a.block,'entry':binding(a.entry_file),'rules':binding(a.rules) if a.rules else None,'fixed_statement':expected_statement,'native_source':binding(native),'baseline':baseline,'sizing':sizing,'memory_jobs':[pre,native_job],'completed_stock_measurements':binding(a.completed_stock_measurements) if a.completed_stock_measurements else None,'cache':a.cache,'cache_purpose':c['result_cache']['purpose'],'runtime_cache_enabled':c['cache_policy']['enabled'],'CPU_external_stop_seconds':search_budget,'memory_claim_report_multiplier':2,'memory_external_stop_bytes':native_job['physical_fence_bytes'],'physical_CPU_limit':'unlimited','no_tactic_timeout':True})
    prestage_sealed(c,out)
    save(out/'RUNTIME.json',c);save(out/'BOUNDARY.json',{'runtime':binding(out/'RUNTIME.json'),'inputs':binding(out/'INPUTS.json'),'invalidation':binding(out/'INVALIDATION.json'),'proof_ran':False,'claims_created':0})
    return out

def check_declaration_target(config):
    if not config.get('declarations_only'):return
    pre,selected=config['jobs']
    target=selected.get('target')
    if (pre['phase']!='prerequisites' or selected['phase']!='native' or
            not target or pre.get('target')!=target):
        raise ValueError('The declaration target differs from its selected carrier.')
    source=Path(config['prepared_workspace'])/config['proof_runtime']['module_files'][target['module']]
    if digest(source)!=target['source_sha256']:
        raise ValueError('The declaration carrier source differs from its target identity.')


def execute(path,expected):
    from command_scope import require
    require()
    try:return execute_retained(path,expected)
    finally:
        from end_run_cleanup import finish
        cleanup_config=read_bound({'path':str(path),'sha256':expected})
        try:finish(cleanup_config,Path(path).parent)
        except Exception as error:print('End-of-run cleanup failed: '+str(error),file=sys.stderr)


def execute_retained(path,expected):
    from command_scope import require
    require()
    path=Path(path);c=read_bound({'path':str(path),'sha256':expected});out=path.parent;__import__('restart_bindings').verify_restart_runtime(c,HERE);check_proof_bindings(c);pre,job=c['jobs'];cache_setting=runtime_cache_setting(c)
    check_declaration_target(c)
    if c.get('dependency_batch') and not c.get('declarations_only'):raise ValueError('Dependency waves cannot execute a native runtime.')
    if c.get('native_route') and cache_setting!='off':raise ValueError('The minimal native route requires cache off.')
    if cache_setting=='on' and os.environ.get('ZESU_IO')=='gate':raise ValueError('A gate cannot enable the checkpoint cache.')
    env=dict(os.environ,PATH='/home/cody/islaris/_opam/bin:/home/cody/.local/bin:/usr/local/bin:/usr/bin:/bin',OPAM_SWITCH_PREFIX='/home/cody/islaris/_opam',PYTHONDONTWRITEBYTECODE='1',PYTHONHASHSEED='0',ZESU_PROOF_CACHE=cache_setting)
    argv=lambda row:[str(PYTHON),'-B',c['job_controller']['path'],str(path),digest(path),row['key'],row['output']]
    if pre['ordered_modules'] or c.get('declaration_checks') or c.get('control_session'):
        reply=subprocess.run(argv(pre),cwd=W,env=env)
        r=read_bound(binding(Path(pre['output'])/'RESULT.json'))
        if not r.get('success'):
            save(out/'RESULT.json',summarize(r,pre['output'],cache_setting));return 2
        helpers=__import__('runpy').run_path(c['adoption_implementation']['path'],run_name='scratch_prerequisite_helpers');helpers['prerequisite_readiness'](c,r)
    elif not c.get('sealed_native_preparation'):
        save(out/'READINESS.json',{'schema':'entry-chain.prerequisite-readiness.v1','objects':[],'existing_compatible_objects':True,'no_compilation_repeated':True})
    if c.get('declarations_only'):
        requested=c.get('declaration_checks',[])
        checked_path=Path(pre['output'])/'native/CONTROL-VERIFICATION.json'
        if requested:
            checked=read_bound(binding(checked_path))
            if [row['specification'] for row in checked]!=requested:
                raise ValueError('The exact declaration checks did not all run.')
            if any(row['result'].get('success') is not True or row['result'].get('verification_method')!='module_m' or row['result'].get('assumptions')!=[] for row in checked):
                raise ValueError('An exact declaration check failed.')
        c['readiness']=binding(out/'READINESS.json')
        c['bindings']=combined_bindings(c['bindings']+[c['readiness']]+read_bound(c['readiness']).get('objects',[]))
        save(out/'READY-RUNTIME.json',c)
        save(out/'RESULT.json',{'status':'control_session_completed' if c.get('control_session') else 'declarations_passed','success':True,'prerequisites':binding(Path(pre['output'])/'RESULT.json'),'native_calls':0,'source_overrides':c['source_overrides'],'exact_statement_check_count':len(requested),'exact_statement_checks':binding(checked_path) if requested else None});return 0
    c['scratch_prior_CPU_seconds']=0
    c['prerequisite_CPU_seconds']=r['CPU']['cpu_seconds'] if pre['ordered_modules'] else 0
    if c.get('sealed_native_preparation'):
        run_path=path
    else:
        c['readiness']=binding(out/'READINESS.json');save(out/'READY-RUNTIME.json',c)
        run_path=out/'READY-RUNTIME.json'
    reply=subprocess.run([str(PYTHON),'-B',c['job_controller']['path'],str(run_path),digest(run_path),job['key'],job['output']],cwd=W,env=env)
    result=read_bound(binding(Path(job['output'])/'RESULT.json'));public=summarize(result,job['output'],cache_setting)
    public.update(inputs=binding(out/'INPUTS.json'),runtime=binding(run_path),prerequisite_CPU=r.get('CPU') if pre['ordered_modules'] else None)
    for field,name in [('closure','CLOSURE.json'),('release','RELEASE.json')]:
        receipt=Path(job['output'])/name
        public[field]=binding(receipt) if receipt.is_file() else None
    public['lifecycle_receipts_unavailable']=[field for field in ['closure','release'] if public[field] is None]
    save(out/'RESULT.json',public)
    from heldout_reporting import summary as visible_summary,selected as held_out
    rule_hashes=[]
    if c.get('native_route'):
        from native_route import authority
        rule_hashes=[{'module':r['module'],'sha256':r['sha256']} for r in authority(c['native_route'])['source_inventory'] if r['module'].startswith('ZesuSsz.Evidence.')]
    visible=visible_summary(job['key'],public,rule_hashes)
    if held_out(job['key']):
        (out/'RESULT.json').chmod(0o600)
        save(out/'PUBLIC-RESULT.json',visible)
    print(json.dumps(visible))
    return 0 if public['status']=='closed' else 1 if public['status']=='open' else 2

def memory_workload_context(config):
    jobs=config.get('jobs')
    if not isinstance(jobs,list) or any(not isinstance(job,dict) for job in jobs):
        raise ValueError('The memory refresh has no valid job list.')
    prerequisites=[job for job in jobs if job.get('phase')=='prerequisites']
    if len(prerequisites)!=1:
        raise ValueError('The memory refresh requires one actual prerequisite job.')
    modules=prerequisites[0].get('ordered_modules')
    mapping=config['proof_runtime']['module_files']
    if (not isinstance(modules,list) or any(not isinstance(name,str) or name not in mapping for name in modules)
            or len(set(modules))!=len(modules)):
        raise ValueError('The actual prerequisite module list is invalid.')
    return dict(config,prerequisite_modules=list(modules))


def refresh_memory(argv):
    from command_scope import require
    require()
    """Rebind admission and harness bytes. Preserve the prepared source seed."""
    parser=argparse.ArgumentParser()
    parser.add_argument('prior_runtime',type=Path);parser.add_argument('prior_sha256')
    parser.add_argument('--end-cleanup',choices=['on','off'],default='on',help='Use off for reusable prefixes, seeds, and queued inputs.')
    parser.add_argument('--seed-reference',type=Path)
    parser.add_argument('--completed-stock-measurements',type=Path,required=True)
    parser.add_argument('--admission-profile',type=Path)
    parser.add_argument('--unadmitted-retirement',type=Path)
    parser.add_argument('--output',type=Path,required=True)
    args=parser.parse_args(argv)
    prior={'path':str(args.prior_runtime.resolve()),'sha256':args.prior_sha256}
    c=read_bound(prior);out=args.output.resolve()
    if args.seed_reference:
        from seed_bindings import compact
        compact(c,binding(args.seed_reference.resolve()),c['prepared_workspace'])
    if out.exists():raise ValueError('The refreshed output already exists.')
    base=Path('/home/cody/zesislar')
    if out.is_relative_to(base):
        rel=out.relative_to(base).parts
        if not (rel[0]=='_build' or len(rel)>2 and rel[0]=='.worktrees' and rel[2]=='_build'):raise ValueError('The refreshed output must be private build data.')
    # A prepared seed can be reused. An active request cannot be duplicated.
    for job in c['jobs']:
        previous=Path(job['output'])
        if (previous/'STARTED.json').exists() and not (previous/'RELEASE.json').exists():
            from memory_policy import validate_unadmitted_retirement
            if not args.unadmitted_retirement:raise ValueError('The prior job has no release; refresh is refused.')
            validate_unadmitted_retirement(binding(args.unadmitted_retirement),previous)
        if (previous/'RELEASE.json').exists() and read_bound(binding(previous/'RELEASE.json')).get('released') is not True:raise ValueError('The prior claim is not released.')
    check_proof_bindings(c)
    measurements=binding(args.completed_stock_measurements.resolve())
    rows=read_bound(measurements)['rows']
    from memory_policy import apply_job
    from memory_policy import workload_for_job
    context=binding(args.admission_profile.resolve()) if args.admission_profile else c.get('admission_profile')
    actual_config=memory_workload_context(c)
    c['jobs']=[dict(apply_job(job,rows,workload_for_job(context,job,actual_config)),output=str(out/'jobs'/job['key'])) for job in c['jobs']]
    if context:c['admission_profile']=context
    from port_native_policy import configure_cpu
    native_job=next(job for job in c['jobs'] if job['phase']=='native')
    search_budget,setup_budget=configure_cpu(c,native_job)
    c.update(runtime_path=str(out/'RUNTIME.json'),shared_latch=str(out/'INFRASTRUCTURE-HOLD.json'),
        readiness={'path':str(out/'READINESS.json'),'sha256':None},scheduler_output=str(out/'scheduler'),
        priority_claim=None,execution_released=True,job_controller=binding(HERE/'code/entry_chain_run.py'),
        scratch_provider=binding(HERE/'code/entry_chain_provider.py'),result_adapter=binding(HERE/'code/entry_chain_result.py'))
    c['guard_override']=binding(HERE/'runtime-tools/resource_guard.sh');c['guard_override_base']=c['guard_override']
    c['admission']=dict(c['admission'],reviewed_helpers=str(HERE/'code/entry_admission'))
    from harness_commit import check
    check(c['harness'])
    implementations=[binding(args.prior_runtime.parent/'HARNESS.json')]
    producers=dict(c['cache_producer_files'])
    producers['implementation']=[dict(row,id='scratch-implementation:'+str(i),kind='source') for i,row in enumerate(implementations)]
    producers['inputs']=[row for row in producers['inputs'] if row.get('id') not in {'completed-stock-memory','admission-profile'} and not row.get('id','').startswith('memory-evidence:')]+[dict(measurements,id='completed-stock-memory',kind='configuration')]+([dict(context,id='admission-profile',kind='configuration')] if context else [])
    c['cache_producer_files']=producers
    from memory_policy import profile_bindings
    memory_inputs=profile_bindings(context)
    producers['inputs'] += [dict(row,id='memory-evidence:'+str(i),kind='configuration') for i,row in enumerate(memory_inputs)]
    additions=[*memory_inputs,prior,measurements,*implementations]+([context] if context else [])+([binding(args.unadmitted_retirement)] if args.unadmitted_retirement else [])
    for job in c['jobs']:
        basis=job.get('completed_stock_measurement')
        if not basis:continue
        evidence=basis['measurement'];legacy=evidence.get('format')=='legacy_r1_workload_rss_v1'
        additions.extend(evidence[name] for name in (['native_source','result','acceptance','release_ledger','compiler'] if legacy else ['native_source','result','closure','release']))
        if evidence.get('declaration_projection'):
            projection=read_bound(evidence['declaration_projection']);additions.extend([evidence['declaration_projection']]+[projection[name] for name in ['current_source','legacy_interval','declaration']])
        if evidence.get('format')=='completed_stock_verification_repair_v1':
            from memory_policy import verification_bindings
            additions.extend(verification_bindings(evidence))
        elif not legacy:additions.append(read_bound(evidence['result'])['complete_state'])
    from end_run_cleanup import policy as cleanup_policy
    c['end_of_run_cleanup']=cleanup_policy(args.end_cleanup=='on')
    c['proof_runtime']['mcp_argv']=python_argv(c['proof_runtime']['mcp_argv'])
    c['adoption_implementation']=binding(HERE/'code/full_chain.py')
    c['bindings']=combined_bindings(c['bindings']+additions+[c['adoption_implementation']])
    if c.get('seed_binding_reference'):
        from seed_bindings import compact
        compact(c,c['seed_binding_reference']['descriptor'],c['prepared_workspace'])
        check_proof_bindings(c)
    # New tools have identical owned shell bytes. Never write the old workspace.
    layout=json.loads((HERE/'TOOL-LAYOUT.json').read_text())
    c['prepared_tool_transition']=[dict(relative=relative,prepared=binding(Path(c['prepared_workspace'])/'tools'/relative),successor=binding(HERE/source)) for relative,source in layout.items()]
    __import__('restart_bindings').verify_restart_runtime(c,HERE)
    out.mkdir(parents=True)
    original_inputs=args.prior_runtime.parent/'INPUTS.json'
    inputs=read_bound(binding(original_inputs)) if original_inputs.exists() else {}
    inputs.update(CPU_external_stop_seconds=search_budget,end_of_run_cleanup=c['end_of_run_cleanup'],memory_refresh={'prior_runtime':prior,'prepared_workspace_unchanged':True,'source_staging_repeated':False,'proof_calls':0,'claims_created':0},completed_stock_measurements=measurements,memory_jobs=c['jobs'])
    save(out/'INPUTS.json',inputs)
    c['bindings']=combined_bindings(c['bindings']+[binding(out/'INPUTS.json')])
    save(out/'RUNTIME.json',c)
    save(out/'BOUNDARY.json',{'runtime':binding(out/'RUNTIME.json'),'inputs':binding(out/'INPUTS.json'),'prior_runtime':prior,'prepared_workspace_unchanged':True,'proof_calls':0,'claims_created':0})
    print(json.dumps({'refreshed':binding(out/'RUNTIME.json'),'source_staging_repeated':False,'proof_calls':0,'claims_created':0}))
    return 0

def main(argv=None):
    argv=sys.argv[1:] if argv is None else argv
    if argv[:1]==['--run']:return execute(argv[1],argv[2])
    if argv[:1]==['--refresh-memory']:return refresh_memory(argv[1:])
    a=arguments(argv);out=prepare(a)
    if a.prepare_only:print(json.dumps({'prepared':binding(out/'BOUNDARY.json'),'proof_calls':0,'claims':0}));return 0
    # Refuse an unchanged failed baseline. It already has a retained native result.
    prior=read_bound({'path':str(a.base_runtime),'sha256':a.base_runtime_sha256})
    baseline_entry=Path(prior['prepared_workspace'])/prior['proof_runtime']['module_files'][ENTRY]
    prior_job=next((row for row in prior['jobs'] if row['phase']=='native' and row['key']==a.block),None)
    previous=Path(prior_job['output'])/'RESULT.json' if prior_job else None
    if not a.source_overrides and not a.declarations_only and a.rules is None and digest(a.entry_file)==digest(baseline_entry) and previous is not None and previous.exists():
        save(out/'UNCHANGED-SEARCH-REFUSED.json',{'reason':'The exact baseline native search already ran.','retained_result':binding(previous)})
        raise ValueError('The unchanged failed search cannot repeat. Supply changed entries or rules.')
    label='rule-scratch-'+a.block+'-'+out.name[:12]
    launch_runtime=read_bound(binding(out/'RUNTIME.json'));check_bindings([launch_runtime['watcher']])
    command=[str(PYTHON),'-B',launch_runtime['watcher']['path'],'watch','--label',label,'--',str(PYTHON),'-B',str(HERE/'scratch.py'),'--run',str(out/'RUNTIME.json'),digest(out/'RUNTIME.json')]
    reply=subprocess.run(command,cwd=W,capture_output=True,text=True);save(out/'WATCHED.json',{'argv':command,'returncode':reply.returncode,'stdout':reply.stdout,'stderr':reply.stderr})
    if reply.returncode:raise RuntimeError('The scratch all-exit watcher did not start.')
    print(json.dumps({'watcher':label,'result':str(out/'RESULT.json'),'boundary':binding(out/'BOUNDARY.json'),'watcher_reply':reply.stdout}));return 0
if __name__=='__main__':
    try:raise SystemExit(main())
    except Exception as error:
        import traceback;print(traceback.format_exc(),file=sys.stderr);raise SystemExit(2)
