import sys,os
sys.dont_write_bytecode=True
os.environ['PYTHONDONTWRITEBYTECODE']='1'
#!/usr/bin/env python3
"""Run one chain block or its shared prerequisites through pinned MCP."""
import asyncio,functools,hashlib,json,os,resource,sys,time,traceback
from pathlib import Path
sys.path[1:1] = [str(Path(__file__).resolve().parents[2]), str(Path(__file__).resolve().parents[3])]
from mcp import ClientSession, StdioServerParameters
from mcp.client.stdio import stdio_client
from scratch_statement import source_statement
from entry_chain import binding,save as atomic_json,check_bindings as bound_rows,digest,relative,strict_loads
from entry_pilot import retain_residual
from entry_pilot_checker import bound_json,complete_groups
from entry_chain_resources import check_operation,normalize_cpu,session_validation
from supplier_ready import ENTRYINTRO_MCP_REFUSAL,entry_intro_plugin_refusal


class ToolFailure(RuntimeError):
    def __init__(self,message,result=None):
        super().__init__(message);self.result=result



HOOKS_MCP_PROJECTION_SHA256='bc30f2f6aa42e50975c20f3577b46b6d9c464234e0d46354ecd8b8bfac581d70'

def hooks_plugin_build(module,source):
    if module!='ZesuSsz.Automation.Hooks':return False
    if digest(source)==HOOKS_MCP_PROJECTION_SHA256:return False
    declarations=[line.strip() for line in source.read_text().splitlines() if line.strip().startswith('Declare ML Module')]
    if declarations != ['Declare ML Module "zesu-signature-gates.plugin".']:
        raise ValueError('The trusted dependency plugin declaration changed.')
    return True


def entry_intro_plugin_build(module,source):
    if module!='ZesuSsz.Automation.EntryIntro':return False
    declarations=[line.strip() for line in source.read_text().splitlines() if line.strip().startswith('Declare ML Module')]
    if not declarations:return False
    if declarations != ['Declare ML Module "zesu-signature-gates.plugin".']:
        raise ValueError('The trusted dependency plugin declaration changed.')
    return True


async def compile_dependency(module,source,workspace,wrapper,flags,output,environment,call,recheck,timeout):
    arguments={'workspace':str(workspace),'file':str(source),
               'timeout':timeout,
               'keep_vo':True,'include_warnings':True}
    refusal_result=None
    if hooks_plugin_build(module,source):
        stem='HOOKS-COMPILE';refusal='Forbidden command Declare ML Module'
    elif entry_intro_plugin_build(module,source):
        try:return await call('rocq_compile_file',arguments)
        except ToolFailure as error:
            if not entry_intro_plugin_refusal(error.result):raise
            refusal_result=error.result
        stem='ENTRYINTRO-COMPILE';refusal=ENTRYINTRO_MCP_REFUSAL
    else:return await call('rocq_compile_file',arguments)
    recheck()
    argv=[str(wrapper)]+flags+[str(source)]
    stdout_path=output/(stem+'.stdout');stderr_path=output/(stem+'.stderr')
    with stdout_path.open('wb') as stdout,stderr_path.open('wb') as stderr:
        child=await asyncio.create_subprocess_exec(*argv,cwd=workspace,env=environment,stdout=stdout,stderr=stderr)
        code=await child.wait()
    recheck()
    result={'success':code==0,'returncode':code,'method':'stock-guarded-dependency-build',
            'MCP_refusal':refusal,'argv':argv,'stdout':binding(stdout_path),
            'stderr':binding(stderr_path),'source':binding(source)}
    if refusal_result is not None:result['MCP_refusal_result']=refusal_result
    atomic_json(output/(stem+'.json'),result)
    if code:raise ToolFailure('The stock dependency build failed.',result)
    return result


def control_step_required(step):
    required=step.get('required',False)
    if type(required) is not bool:raise ValueError('The control requirement must be Boolean.')
    return required

def require_control_result(required,result):
    if required and result.get('success') is not True:
        raise ToolFailure(result.get('error') or 'A required control step failed.',result)

def prerequisite_environment(runtime,workspace,output,inherited=None):
    environment=dict(os.environ if inherited is None else inherited)
    for key in list(environment):
        if key.startswith('ENTRY_CHAIN_COMPILER_SNAPSHOT_'):
            environment.pop(key)
    for key in list(environment):
        if key.startswith(('ROCQ_','COQC_')) or key in {'COQPATH','COQBIN','COQC','OCAMLPATH','ZESU_WRITER_ID','ZESU_WRITER_MAX_COQC','ZESU_COQC_RESERVATION','ZESU_COQC_SCOPE'}:
            environment.pop(key)
    environment.update(PATH='/home/cody/islaris/_opam/bin:/usr/local/bin:/usr/bin:/bin',
        OPAM_SWITCH_PREFIX='/home/cody/islaris/_opam',ROCQ_WORKSPACE=str(workspace),ROCQ_DUNE_BUILD='0',
        ROCQ_COQC_BINARY=str(workspace/relative(runtime['coqc_wrapper'])),
        ROCQ_COMPILE_MULTI_ERROR_CAP='0',ROCQ_MAX_PET_RSS_MB='65536',
        ROCQ_QUERY_TIMEOUT_CAP='604800',ROCQ_PET_TIMEOUT='604800',
        ZESU_COMPLETE_GOAL_DIR=str(output/'complete-goals'),ZESU_DIAGNOSTIC_PROBE='1',
        ZESU_PROBE_ISSUE='10',ZESU_MODULE_LIMIT_GIB='64',ZESU_GATE_MODULE_LIMIT_GIB='64',
        ZESU_PROOF_CPU_LIMIT='unlimited',ZESU_SCOPE_CPU='unlimited',
        OCAMLPATH=runtime['ocamlpath'].replace('{workspace}',str(workspace)),
        AGENT_BUILD_DIR=str(workspace/relative(runtime['build_dir'])),
        ENTRY_CHAIN_RUNTIME_JSON=runtime['runtime_path'],
        ENTRY_CHAIN_RUNTIME_SHA256=runtime['runtime_sha256'])
    from memory_policy import environment as memory_environment
    environment.update(memory_environment(runtime['phase'],runtime.get('canonical_admission',{}).get('minimum_claim_bytes'),job=runtime.get('canonical_admission',{}).get('memory_job')))
    return environment


def proof_environment(runtime,workspace,output,inherited=None):
    if runtime['phase']!='native':return prerequisite_environment(runtime,workspace,output,inherited)
    directory=Path(runtime['prospective_directory'])
    boundary=strict_loads((directory/'ACTUAL-BOUNDARY.json').read_text())
    bound_rows([boundary['environment'],boundary['phase2'],boundary['key_equality'],boundary['mcp_launch']])
    equality=strict_loads(Path(boundary['key_equality']['path']).read_text())
    if equality.get('equal') is not True or equality.get('proof_calls_between_phases')!=0:
        raise ValueError('The two-phase proof inputs do not match.')
    environment=strict_loads(Path(boundary['environment']['path']).read_text())
    if environment['ENTRY_CHAIN_RUNTIME_JSON']!=runtime['runtime_path'] or environment['ENTRY_CHAIN_RUNTIME_SHA256']!=runtime['runtime_sha256']:
        raise ValueError('The actual environment names another runtime envelope.')
    if environment['ZESU_AGGREGATE_SLICE']!=os.environ.get('ZESU_AGGREGATE_SLICE'):
        raise ValueError('The actual aggregate differs from its typed transport.')
    return environment


def declaration_search_fixture(source, specification, output, side):
    """Copy the exact native declaration. Do not execute its native proof."""
    original_sha = digest(source)
    problem = specification['prefix'] + specification['statement'] + specification.get('pre_proof_commands','')
    if not problem.endswith('\n'):
        raise ValueError('The native declaration must end before its Proof line.')
    fixture = source.with_name(source.stem + '_EntryPilotSearch.v')
    if fixture.exists():
        raise ValueError('The owned search fixture already exists.')
    fixture.write_text(problem + 'Proof.\nAbort.\n')
    proof_line = problem.count('\n')
    if fixture.read_text().splitlines()[proof_line] != 'Proof.':
        raise ValueError('The search cursor does not select its Proof sentence.')
    if digest(source) != original_sha:
        raise ValueError('The search fixture changed its native source.')
    atomic_json(output/(side+'-SEARCH-FIXTURE.json'), {
        'original_source': str(source), 'original_source_sha256': original_sha,
        'prefix_sha256': hashlib.sha256(specification['prefix'].encode()).hexdigest(),
        'statement_sha256': hashlib.sha256(specification['statement'].encode()).hexdigest(),
        'fixture': str(fixture), 'fixture_sha256': digest(fixture),
        'line': proof_line, 'character': 0, 'suffix': 'Proof.\nAbort.\n'})
    return fixture, proof_line


def validated_session(function):
    @functools.wraps(function)
    async def wrapped(request):
        state=None
        try:
            with session_validation(request['runtime'],request['runtime_sha256']) as state:
                result=await function(request)
            if state.final is None or state.final.get('success') is not True:
                raise ValueError('The provider session lacks successful final validation.')
            output=Path(request['output'])
            atomic_json(output/'PROGRESS.json',{'phase':'complete'})
            atomic_json(output/'TRANSPORT-CLOSED.json',{'normal_context_exit':True})
            return result
        finally:
            if state is not None:
                atomic_json(Path(request['output'])/'SESSION-VALIDATION.json',state.report())
    return wrapped


@validated_session
async def execute(request):
    runtime = bound_json(request['runtime'], request['runtime_sha256'])
    if runtime.get('dependency_batch') and runtime.get('phase')!='prerequisites':
        raise ValueError('Dependency waves cannot execute in native phase.')
    runtime.update(runtime_path=request['runtime'],runtime_sha256=request['runtime_sha256'])
    workspace, output = Path(request['workspace']), Path(request['output'])
    environment = proof_environment(runtime, workspace, output)
    from coqc_findlib import compiler_environment
    compiler_context=compiler_environment(workspace,environment)
    from compiler_snapshot import publish
    snapshot=publish(runtime,lambda:check_operation(runtime,force_full=True),
                     Path(request['output'])/'COMPILER-SNAPSHOT.json',environment=compiler_context)
    accepted_objects=None
    if snapshot is not None:
        from compiler_snapshot import OutputReceipts,read as read_snapshot
        accepted_objects=OutputReceipts(read_snapshot(snapshot,{'path':request['runtime'],'sha256':request['runtime_sha256']}),snapshot)
    row = runtime['target']
    workspace, output = Path(request['workspace']), Path(request['output'])
    atomic_json(output/'PROGRESS.json', {'phase': 'prepared_inputs', 'identity': request['identity']})
    ordered = runtime.get('ordered_modules', [])
    from native_route import validate_runtime
    native_body=validate_runtime(runtime,workspace) if runtime['phase']=='native' else 'zesu_block.'
    calls, receipts = [], {}
    if snapshot is not None:
        environment.update(ENTRY_CHAIN_COMPILER_SNAPSHOT_JSON=snapshot['path'],
                           ENTRY_CHAIN_COMPILER_SNAPSHOT_SHA256=snapshot['sha256'],
                           ENTRY_CHAIN_COMPILER_SNAPSHOT_OUTPUT_KEY=accepted_objects.key)
    launcher = [word.replace('{workspace}', str(workspace)) for word in runtime['mcp_argv']]
    from native_instruction_profile import checked_launcher,complete_profile
    instruction_profile=None
    if runtime['phase']=='native':
        launcher,instruction_profile=checked_launcher(
            runtime.get('canonical_admission',{}).get('memory_job'),row,workspace,output,launcher,
            Path(runtime['prospective_directory']))

    dependency_spec=runtime.get('dependency_batch')
    dependency_plan=None
    if dependency_spec:
        dependency_context={
            'phase':runtime['phase'],
            'canonical_admission':runtime['canonical_admission'],
            'native_route':runtime.get('native_route'),
            'control_session':runtime.get('control_session'),
            'physical_flags':runtime['physical_flags'],
            'module_files':runtime['module_files'],
            'build_dir':runtime['build_dir'],
            'dependency_batch':dependency_spec}
        from dependency_batch import validate_projection as validate_dependency_batch
        dependency_plan,_=validate_dependency_batch(dependency_context,workspace,ordered,dependency_spec)
    completed_dependencies=set()
    wave_modules={} if dependency_plan is None else {name:index for index,wave in enumerate(dependency_plan['waves']) for name in wave['modules']}

    async def call(session, name, arguments):
        precheck=check_operation(runtime)
        entry = {'tool': name, 'arguments': arguments, 'started_ns': time.time_ns(),
                 'pre_operation_validation':precheck}
        calls.append(entry)
        atomic_json(output/'CALLS.json', calls)
        native_search = runtime['phase']=='native' and name=='rocq_check' and arguments.get('body')==native_body
        if native_search:
            from scratch_limits import record_search_origin
            record_search_origin(output.parent, entry['started_ns'], arguments,native_route=runtime.get('native_route'))
        try:
            raw = await session.call_tool(name, arguments)
            if native_search:
                from scratch_limits import record_search_end
                record_search_end(output.parent)
            entry['raw_response'] = raw.model_dump(mode='json', by_alias=True)
            atomic_json(output/'CALLS.json', calls)
            value = raw.structuredContent
            if not isinstance(value, dict):
                value = strict_loads(next(part.text for part in raw.content if part.type == 'text'))
            entry['result'] = value
            entry['ended_ns'] = time.time_ns()
            atomic_json(output/'CALLS.json', calls)
            if value.get('pet_restarted') or value.get('restarted') or value.get('reason') in {'unavailable','memory_exhausted','timeout'}:
                atomic_json(output/'INFRASTRUCTURE-FAILURE.json',{'tool':name,'result':value})
            if value.get('pet_restarted') or value.get('restarted'):
                raise ToolFailure('PET restarted. The attempt must stop.', value)
            if raw.isError or not (value.get('success') or name == 'rocq_health' and value.get('ok')):
                raise ToolFailure('The proof tool returned failure.', value)
            if name == 'rocq_compile_file':
                compiled_source = Path(arguments['file'])
                compiled_object = compiled_source.with_suffix('.vo')
                if compiled_object.is_file():
                    atomic_json(output/('COMPILE-OBJECT-%04d.json'%len(calls)),
                        {'tool_result': value, 'source': binding(compiled_source),
                         'object': binding(compiled_object), 'before_later_checks': True})
            entry['post_operation_validation']=check_operation(runtime)
            entry['validation_finished_ns']=time.time_ns()
            if name=='rocq_compile_file' and compiled_object.is_file() and accepted_objects is not None:
                entry['accepted_object_receipt']=accepted_objects.accept(compiled_source,compiled_object,
                    '/home/cody/islaris/_opam/bin/coqc',runtime['physical_flags'],value)
            atomic_json(output/'CALLS.json',calls)
            return value
        except BaseException:
            entry['private_error'] = traceback.format_exc()
            atomic_json(output/'CALLS.json', calls)
            raise

    async def export(session, state):
        value = await call(session, 'rocq_complete_goals', {'from_state': state['state_id']})
        complete_groups(value)
        atomic_json(output/'LAST-COMPLETED-STATE.json',{'export':value,
            'state_source':'completed_checkpoint','state_id':state['state_id'],
            'captured_ns':time.time_ns()})
        return value

    def retain_first(value, side, qualifier, state_source):
        directory = output/'first-residual'
        if not directory.exists():
            directory.mkdir(mode=0o700)
            retained = retain_residual(value, directory)
            # The helper's excerpt remains private. The outer checker never sends it.
            atomic_json(directory/'PRIVATE-INDEX.json', {'side': side, 'qualifier': qualifier,
                                                       'retained': retained, 'state_source': state_source, 'agent_visible': False})

    timeout = 604800
    try:
        async with stdio_client(StdioServerParameters(command=launcher[0], args=launcher[1:],
                                                      env=environment, cwd=str(workspace))) as streams:
            async with ClientSession(*streams) as session:
                await session.initialize()
                await call(session, 'rocq_health', {})
                targets = {row['block']['module']} if runtime['phase'] == 'native' else set()
                for module in ordered:
                    if module in completed_dependencies:continue
                    if module in wave_modules:
                        from dependency_batch import run_wave
                        check_operation(runtime)
                        atomic_json(output/'PROGRESS.json',{'phase':'dependency_wave','module':module,'wave':wave_modules[module]})
                        await asyncio.to_thread(run_wave,wave_modules[module],dependency_context,workspace,output,ordered,completed_dependencies,environment,recheck=lambda:check_operation(runtime))
                        check_operation(runtime)
                        continue
                    if module in targets:
                        continue
                    source = workspace/relative(runtime['module_files'][module])
                    atomic_json(output/'PROGRESS.json', {'phase': 'dependency_compile', 'module': module})
                    result=await compile_dependency(module,source,workspace,
                        workspace/relative(runtime['coqc_wrapper']),runtime['expected_mcp_flags'],output,environment,
                        lambda name,args:call(session,name,args),lambda:check_operation(runtime),timeout)
                    obj = source.with_suffix('.vo')
                    if not obj.is_file():
                        raise ToolFailure('A dependency object is absent after compilation.')
                    if accepted_objects is not None and hooks_plugin_build(module,source):
                        check_operation(runtime)
                        accepted_objects.accept(source,obj,'/home/cody/islaris/_opam/bin/coqc',runtime['physical_flags'],result)
                    atomic_json(output/('dependency-'+module+'.json'), {'source': str(source),
                        'source_sha256': digest(source), 'object': str(obj), 'object_sha256': digest(obj),
                        'result': result})
                if runtime['phase']=='prerequisites':
                    verified_controls=[]
                    for specification in runtime.get('declaration_checks',[]):
                        result=await call(session,'rocq_verify',dict(specification,workspace=str(workspace),timeout=timeout))
                        if result.get('verification_method')!='module_m' or result.get('assumptions')!=[]:
                            raise ToolFailure('The control statement did not pass exact kernel verification.',result)
                        verified_controls.append({'specification':specification,'result':result})
                    atomic_json(output/'CONTROL-VERIFICATION.json',verified_controls)
                if runtime.get('control_session'):
                    specification=runtime['control_session']
                    source=workspace/relative(runtime['module_files'][specification['module']])
                    start_source=source
                    if specification.get('fixture'):
                        prefix=source.read_text().splitlines(keepends=True)[:specification['line']+1]
                        if prefix[-1].strip()!='Proof.':raise ValueError('The control fixture must end at its Proof sentence.')
                        start_source=source.with_name('RuleScratchControlSession.v')
                        if start_source.exists():raise ValueError('The control fixture exists.')
                        start_source.write_text(''.join(prefix)+'Abort.\n')
                        atomic_json(output/'CONTROL-SESSION-FIXTURE.json',{'original':binding(source),'fixture':binding(start_source),'prefix_lines':len(prefix),'proof_source_unchanged':True})
                    started=await call(session,'rocq_start',dict(workspace=str(workspace),file=str(start_source),line=specification['line'],character=specification.get('character',0),timeout=timeout))
                    states={'start':started['state_id']};observations=[]
                    for step in specification['steps']:
                        required=control_step_required(step)
                        try:
                            result=await call(session,'rocq_check',dict(from_state=states[step['from']],body=step['body'],timeout=timeout))
                        except ToolFailure as error:
                            result=error.result
                            if not isinstance(result,dict) or result.get('reason') in {'unavailable','memory_exhausted','timeout'}:raise
                        if result.get('success') and result.get('state_id') is not None:states[step['name']]=result['state_id']
                        observation={'name':step['name'],'result':result};observations.append(observation)
                        atomic_json(output/'CONTROL-SESSION.json',{'source':binding(source),'specification':specification,'observations':observations,'native_calls':0})
                        require_control_result(required,result)
                        if step.get('export') and result.get('success'):
                            atomic_json(output/('CONTROL-GROUPS-'+step['name']+'.json'),await export(session,result))
                for side in (('block',) if runtime['phase'] == 'native' else ()):
                    target = row[side]
                    source = workspace/relative(runtime['module_files'][target['module']])
                    if digest(source) != target['source_sha256']:
                        raise ValueError('The native source changed.')
                    specification = source_statement(source,native_body)
                    statement_sha = hashlib.sha256(specification['statement'].encode()).hexdigest()
                    if statement_sha != target['statement_sha256']:
                        raise ValueError('The original public statement changed.')
                    search_fixture, proof_line = declaration_search_fixture(
                        source, specification, output, side)
                    state = await call(session, 'rocq_start', {'workspace': str(workspace),
                        'file': str(search_fixture), 'theorem': '', 'line': proof_line,
                        'character': 0, 'timeout': timeout})
                    pre_call_export = await export(session, state)
                    atomic_json(output/'PRE-CALL-STATE.json', {
                        'side': side, 'export': pre_call_export,
                        'state_source': 'retained_pre_call_state',
                        'requested_body': native_body,
                        'qualifier': 'Complete pre-call state. This is not the interrupted internal stopping state.'})
                    before = state
                    atomic_json(output/'PROGRESS.json', {'phase': 'native_search', 'side': side,
                        'statement': specification['statement'], 'identity': request['identity']})
                    try:
                        state = await call(session, 'rocq_check', {'from_state': state['state_id'],
                            'body': native_body, 'timeout': timeout})
                    except ToolFailure as error:
                        error_result = error.result if isinstance(error.result, dict) else {}
                        returned_id = error_result.get('state_id', error_result.get('last_valid_state_id'))
                        has_returned_state = returned_id is not None
                        state_source = ('returned_error_state' if error_result.get('state_id') is not None else 'reported_last_valid_state') if has_returned_state else 'retained_pre_call_state'
                        atomic_json(output/'NATIVE-ERROR.json', {'side': side, 'complete_error_result': error_result,
                            'raw_response': calls[-1].get('raw_response'), 'state_source': state_source,
                            'selected_state_id': returned_id if has_returned_state else before['state_id']})
                        if not any(item.get('result', {}).get('pet_restarted') or item.get('result', {}).get('restarted') for item in calls):
                            value = await export(session, {'state_id': returned_id} if has_returned_state else before)
                            qualifier = ('Complete state returned with the failed command.' if has_returned_state else
                                         'Last retained pre-call state. The internal failure residual is unavailable.')
                            retain_first(value, side, qualifier, state_source)
                        raise
                    final_export = await export(session, state)
                    groups = complete_groups(final_export)
                    if any(groups[key] for key in ('goals', 'stack', 'shelf', 'given_up')):
                        retain_first(final_export, side, 'Complete residual after the single native tactic.', 'successful_command_returned_state')
                        raise ToolFailure('The native tactic left residual obligations.')
                    atomic_json(output/'PROGRESS.json', {'phase': 'Qed', 'side': side})
                    ended = await call(session, 'rocq_check', {'from_state': state['state_id'],
                        'body': 'Qed.', 'timeout': timeout})
                    if not ended.get('proof_finished'):
                        raise ToolFailure('Qed did not finish the native proof.')
                    atomic_json(output/'PROGRESS.json', {'phase': 'native_compile', 'side': side})
                    compiled = await call(session, 'rocq_compile_file', {'workspace': str(workspace),
                        'file': str(source), 'timeout': timeout, 'keep_vo': True, 'include_warnings': True})
                    obj = source.with_suffix('.vo')
                    if not obj.is_file():
                        raise ToolFailure('The native compiler did not retain its object.')
                    obj_sha = digest(obj)
                    name = 'check_entry_exact_'+side
                    declaration = specification['statement'].replace('Lemma '+specification['name'], 'Lemma '+name, 1)
                    problem = specification['prefix']+declaration
                    proof = (specification['prefix']+'Require Import '+target['module']+'.\n'+declaration+
                             'Proof. apply '+target['module']+'.'+specification['name']+'. Qed.\n')
                    atomic_json(output/(side+'-EXACT.json'), {'problem_statement': problem,
                        'proof': proof, 'problem_name': name, 'original_statement_sha256': statement_sha})
                    atomic_json(output/'PROGRESS.json', {'phase': 'exact_verification', 'side': side})
                    verified = await call(session, 'rocq_verify', {'workspace': str(workspace),
                        'problem_statement': problem, 'proof': proof, 'problem_name': name, 'timeout': timeout})
                    if verified.get('verification_method') != 'module_m' or verified.get('assumptions') != []:
                        raise ToolFailure('The exact check did not return module_m with empty assumptions.')
                    if digest(obj) != obj_sha:
                        raise ToolFailure('The exact check changed the retained native object.')
                    receipts[side] = {'statement': specification['statement'], 'identity': request['identity'],
                        'statement_sha256': statement_sha, 'native_tactic': native_body[:-1],
                        'compile_file_success': compiled['success'], 'verification_method': 'module_m',
                        'assumptions': [], 'final_export': final_export,
                        'source': str(source), 'source_sha256': digest(source),
                        'object': str(obj), 'object_sha256': obj_sha}
                    if runtime.get('native_route'):receipts[side]['native_route']=runtime['native_route']
                    atomic_json(output/'NATIVE-RESULTS.json', receipts)
                await call(session, 'rocq_health', {})
    finally:
        complete_profile(instruction_profile,output)
        atomic_json(output/'NATIVE-RESULTS.json', receipts)


if __name__=='__main__':
    request=strict_loads(Path(sys.argv[1]).read_text())
    try:
        normalize_cpu()
        asyncio.run(execute(request))
    except BaseException:
        atomic_json(Path(request['output'])/'WORKER-FAILURE.json',{'private_error':traceback.format_exc()})
        raise SystemExit(1)
