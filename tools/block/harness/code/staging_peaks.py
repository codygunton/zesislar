"""Measure preparation in dedicated guarded leaves before a proof runtime exists."""
from pathlib import Path
import copy
import hashlib
import json
import os
import subprocess
import sys
import uuid

from entry_chain import binding, read_bound
from role_peaks import private_document, fence, identity, run_payload, finish

SCHEMA = 'entry-chain.staging-peak-context.v1'
ROLES = ('public-prepare', 'owned-staging')
KEYS = ('ZESU_STAGING_CONTEXT_JSON', 'ZESU_STAGING_CONTEXT_SHA256')
GIB = 1024**3


def workload(root):
    """Match executable workload bytes, independently of revision and output names."""
    root = Path(root)
    paths = [root/'tools/block/harness/scratch.py', root/'tools/block/harness/command_scope.py']
    paths += sorted((root/'tools/block/harness/code').rglob('*.py'))
    paths += [root/'tools/module_memory.py', root/'tools/resource_guard.sh',
              root/'tools/block/harness/runtime-tools/resource_guard.sh']
    rows = [(str(path.relative_to(root)), binding(path)['sha256']) for path in paths]
    return hashlib.sha256(json.dumps(rows, separators=(',', ':')).encode()).hexdigest()


def input_workload(role, command, configuration=None, job=None):
    """Keep material inputs exact. Relocate only the new output namespace."""
    from proof_cache_key import identity as key_identity
    if role == ROLES[0]:
        words=[];arguments=iter(command[3:])
        for word in arguments:
            if word == '--output':
                next(arguments);words.extend([word,'{output}']);continue
            if word.startswith('--output='):
                words.append('--output={output}');continue
            if word == '--harness-commit':
                next(arguments);words.extend([word,'{executable-workload}']);continue
            if word.startswith('--harness-commit='):
                words.append('--harness-commit={executable-workload}');continue
            name,separator,target=word.partition('=')
            candidate=target if separator and name.startswith('--') else word
            path=Path(candidate)
            words.append({'argument':word,'file':binding(path)} if path.is_file() else word)
        value={'arguments':words}
    else:
        configuration=copy.deepcopy(configuration)
        # These fields identify the transport document, not its workload.
        configuration.pop('runtime_sha256',None)
        root=str(Path(configuration['runtime_path']).parent) if configuration.get('runtime_path') else None
        configuration.pop('runtime_path',None)
        harness=configuration.get('harness',{})
        harness_root=harness.get('root')
        # Executable source bytes bind the revision independently above.
        for key in ('commit','tree','tools_tree'):
            harness.pop(key,None)
        def relocated(value):
            if isinstance(value,dict):return {key:relocated(child)for key,child in value.items()}
            if isinstance(value,list):return [relocated(child)for child in value]
            if isinstance(value,str):
                for prefix,label in ((root,'{output}'),(harness_root,'{harness}')):
                    if prefix and (value==prefix or value.startswith(prefix+'/')):
                        return label+value[len(prefix):]
            return value
        value=relocated({'configuration':configuration,'job':{key:val for key,val in job.items()if key!='policy'}})
    return key_identity('entry-chain.staging-inputs.v1',value)


def configuration_value(reference, derived=None):
    value=read_bound(reference)
    for key,item in (derived or {}).items():
        if key=='runtime_path' and item==reference['path'] or key=='runtime_sha256' and item==reference['sha256']:
            if key in value and value[key]!=item:
                raise ValueError('The derived staging runtime identity changed.')
            value[key]=item
        else:raise ValueError('The staging configuration adds unsupported state.')
    return value


def run_kind(role, arguments=None, job=None, config=None):
    if role == ROLES[0]:
        arguments = list(arguments)
        if (not arguments or arguments[0] in ('--run', '--refresh-memory')
                or '--prepare-only' not in arguments
                or any(word in ('--run', '--refresh-memory') for word in arguments)):
            raise ValueError('A public preparation role requires prepare-only.')
        return 'prepare-declarations' if '--declarations-only' in arguments else 'prepare-native'
    if role == ROLES[1]:
        if job['phase'] not in ('native', 'prerequisites'):
            raise ValueError('The staging job has another phase.')
        return 'staging-' + job['phase'] + ('-dag' if config.get('declaration_dag') else '-serial')
    raise ValueError('The staging role is unsupported.')


def context(reference, reader):
    value, _ = private_document(reference, reader)
    if (not isinstance(value,dict) or value.get('schema') != SCHEMA or value.get('role') not in ROLES
            or type(value.get('claim_bytes')) is not int or value['claim_bytes'] <= 0
            or type(value.get('default_claim_bytes')) is not int
            or not 0 < value['claim_bytes'] <= value['physical_fence_bytes']):
        raise ValueError('The staging context has another role or booking.')
    from harness_commit import check
    check(value['harness'])
    root = Path(value['harness']['root'])
    if value['workload'] != workload(root):
        raise ValueError('The staging workload source changed.')
    command = value['command']
    if value['role'] == ROLES[0]:
        script = root/'tools/block/harness/scratch.py'
        if command[:3] != [value['python'], '-B', str(script)]:
            raise ValueError('The preparation command changed.')
        expected = run_kind(ROLES[0], command[3:])
    else:
        configuration = configuration_value(value['configuration'],value.get('derived_configuration'))
        job = value['job']
        jobs = [row for row in configuration['jobs'] if row['key'] == job['key']]
        if (len(jobs) != 1 or {k:v for k,v in job.items() if k != 'policy'} != jobs[0]
                or configuration['harness'] != value['harness']
                or job['output'] != value['output']
                or job['physical_fence_bytes'] != value['physical_fence_bytes']
                or job['claim_bytes'] != value['default_claim_bytes']):
            raise ValueError('The owned staging configuration changed.')
        script = root/'tools/block/harness/code/staging_peaks.py'
        if command != [value['python'], '-B', str(script), '--execute', reference['path'], reference['sha256']]:
            # The self reference is supplied separately to avoid a circular digest.
            if command != [value['python'], '-B', str(script), '--execute']:
                raise ValueError('The owned staging command changed.')
        expected = run_kind(ROLES[1], job=job, config=configuration)
    material=input_workload(value['role'],command,configuration if value['role']==ROLES[1] else None,value['job'])
    if material!=value.get('input_workload'):
        raise ValueError('The staging material inputs changed.')
    if expected != value['run_kind']:
        raise ValueError('The staging context has another run kind.')
    if (value['producer'] != binding(root/'tools/block/harness/code/staging_peaks.py')
            or value['controller'] != binding(root/'tools/block/harness/code/entry_chain_run.py')):
        raise ValueError('The staging producer source changed.')
    return value


def registry_context(environment, actor, reader):
    import run_registry as registry
    run_id=environment['ZESU_RUN_ID']
    store=registry.default_store()
    row=registry.Registry(store).read_run(run_id)
    reader.ancestry(actor['pid'],row['scheduler'])
    if not any({key:job[key]for key in ('pid','startticks')}==actor for job in row['jobs']):
        raise ValueError('The staging scope actor lacks its exact registry row.')
    return {'store':str(store),'run_id':run_id,'scheduler':row['scheduler'],
            'owner':row['owner'],'source':binding(Path(registry.__file__))}


def closed_registry(reference, reader):
    import admission_memory as memory
    import run_registry as registry
    from entry_chain import check_bindings
    check_bindings([reference['source']])
    row=registry.Registry(reference['store']).read_run(reference['run_id'])
    if (row['scheduler']!=reference['scheduler'] or row['owner']!=reference['owner']
            or row.get('status') not in ('completed','failed')
            or type(row.get('exit_code'))is not int or not 0<=row['exit_code']<=255
            or row.get('all_actors_closed')is not True
            or any(claim.get('released')is not True for claim in row['claims'].values())
            or not all(memory.ended_process(reader,actor)for actor in [row['scheduler'],*row['jobs']])):
        raise ValueError('The staging registry lacks exact normal closure.')


def _released(reference, entry, data, reader, role, kind, source):
    import admission_memory as memory
    value, file_identity = private_document(reference, reader)
    if (not isinstance(value,dict) or value.get('schema') != 'zesu.guard.controller-exit.v1'
            or list(file_identity) != entry['file_identity']
            or value.get('role') != role or value.get('run_kind') != kind
            or type(value.get('returncode')) is not int or not 0 <= value['returncode'] <= 255
            or type(value.get('memory_peak_bytes')) is not int or value['memory_peak_bytes'] <= 0):
        raise ValueError('The staging exit lacks an exact normal status and peak.')
    selected = context(value['context'], reader)
    if selected['role'] != role or selected['run_kind'] != kind or (selected['workload'],selected['input_workload']) != source:
        raise ValueError('The staging exit has another workload.')
    key = value['claim_key']; owner = data['shell_claim_owners'][key]
    attestation = owner['guard_attestation']
    if (owner != value['owner_record'] or owner['guard_source'] != value['guard_source']
            or attestation['actor'] != value['scope_actor'] or attestation['leaf'] != value['scope']
            or data['fixed_claims'].get(key) != 0
            or data['shell_releases'][key]['owner'] != owner['owner']
            or data['shell_releases'][key]['marker'] != owner['marker']
            or Path(owner['marker']).exists() or Path(value['scope']['scope']).exists()
            or value.get('payload_process_group_closed') is not True
            or not all(memory.ended_process(reader, actor) for actor in
                (owner['owner'], value['scope_actor'], value['payload_actor'], selected['owner']))
            or value['physical_fence_bytes'] != selected['physical_fence_bytes']):
        raise ValueError('The staging exit lacks exact closed and released ownership.')
    if reader.guard_source(value['guard_source']['path'], value['guard_source']['sha256']) != value['guard_source']:
        raise ValueError('The staging guard source changed.')
    closed_registry(value['staging_registry'],reader)
    if role == ROLES[1] and selected.get('canonical_root') is not None:
        root=value['root_claim_key']; root_owner=value['root_owner']
        release=data['entry_pilot_outside_releases'][root]
        closure=read_bound(release['closure'])
        if (data['fixed_claims'].get(root)!=0
                or data['entry_pilot_outside_owners'].get(root)!=root_owner
                or release['owner']!=root_owner or release['bytes']!=selected['default_claim_bytes']
                or closure.get('owner')!=root_owner or closure.get('all_owned_actors_closed') is not True):
            raise ValueError('The owned staging root lacks exact release and closure.')
    return value


def recorded(reference, role, kind, source, *, ledger=None, reader=None):
    import admission_memory as memory
    reader = reader or memory.ScopeReader()
    ledger = Path(ledger or os.environ.get('ZESU_CANONICAL_LEDGER', memory.DEFAULT_LEDGER))
    with memory.ledger_transaction(ledger) as data:
        data = copy.deepcopy(data)
    entries = [row for row in data.get('controller_exit_peaks', []) if row.get('receipt') == reference]
    if len(entries) != 1:
        raise ValueError('The staging exit lacks one guard endorsement.')
    return _released(reference, entries[0], data, reader, role, kind, source)


def last_peak(role, kind, source, *, ledger=None, reader=None):
    import admission_memory as memory
    reader = reader or memory.ScopeReader()
    ledger = Path(ledger or os.environ.get('ZESU_CANONICAL_LEDGER', memory.DEFAULT_LEDGER))
    try:
        with memory.ledger_transaction(ledger) as data:
            data = copy.deepcopy(data)
        for row in reversed(data.get('controller_exit_peaks', [])):
            if not isinstance(row,dict):
                return None
            if row.get('role') != role or row.get('run_kind') != kind:
                continue
            value = _released(row['receipt'], row, data, reader, role, kind, source)
            return row['receipt'], value['memory_peak_bytes']
    except (KeyError, OSError, TypeError, ValueError):
        pass
    return None


def create(role, harness, command, default, limit, *, job=None, configuration=None, output=None, environment=None, derived=None, canonical_root=None):
    import admission_memory as memory
    from scope_bookings import reset_controller
    source = workload(harness['root'])
    config = configuration_value(configuration,derived) if configuration else None
    kind = run_kind(role, command[3:] if role == ROLES[0] else None, job, config)
    material=input_workload(role,command,config,job)
    peak = last_peak(role, kind, (source,material))
    claim = max(GIB, (3*peak[1]+1)//2) if peak else default
    # A completed peak cannot authorize a booking above the unchanged fence.
    if claim > limit:
        peak = None; claim = default
    if not 0 < claim <= limit:
        raise ValueError('The staging booking exceeds its physical fence.')
    env = reset_controller(os.environ if environment is None else environment)
    for name in ('ZESU_COQC_SCOPE', 'ZESU_COQC_RESERVATION', 'ZESU_OWNED_GUARD_TOKEN', 'ZESU_MODULE_MEMORY_PROFILE', *KEYS):
        env.pop(name, None)
    directory = Path(env.get('ZESU_CANONICAL_LEDGER', memory.DEFAULT_LEDGER)).parent/'staging-contexts'
    directory.mkdir(mode=0o700, exist_ok=True)
    path = directory/(uuid.uuid4().hex+'.json')
    value = {'schema':SCHEMA, 'role':role, 'run_kind':kind, 'harness':harness,
        'workload':source, 'input_workload':material, 'derived_configuration':derived,
        'canonical_root':canonical_root, 'python':command[0], 'command':command, 'owner':identity(os.getpid()),
        'claim_bytes':claim, 'default_claim_bytes':default, 'physical_fence_bytes':limit,
        'producer':binding(Path(harness['root'])/'tools/block/harness/code/staging_peaks.py'),
        'controller':binding(Path(harness['root'])/'tools/block/harness/code/entry_chain_run.py'),
        'selected_peak':peak[0] if peak else None, 'configuration':configuration, 'job':job, 'output':output}
    with open(path,'x',opener=lambda name,flags:os.open(name,flags,0o600))as stream:
        json.dump(value,stream,sort_keys=True);stream.write('\n')
    reference = binding(path)
    env.update({KEYS[0]:reference['path'],KEYS[1]:reference['sha256'],
                'ZESU_MODULE_CLAIM_BYTES':str(claim)})
    return reference, value, env


def payload(reference, value):
    return value['command'] + ([reference['path'],reference['sha256']] if value['role'] == ROLES[1] else [])


def begin(marker, command, *, ledger=None, reader=None, environment=None):
    import admission_memory as memory
    reader = reader or memory.ScopeReader(); env = os.environ if environment is None else environment
    reference = {'path':env[KEYS[0]],'sha256':env[KEYS[1]]}
    selected = context(reference,reader)
    if command != payload(reference,selected) or env.get('ZESU_MODULE_CLAIM_BYTES') != str(selected['claim_bytes']):
        raise ValueError('The guarded staging payload or claim changed.')
    peak = selected['selected_peak']
    expected = selected['default_claim_bytes']
    if peak is not None:
        value = recorded(peak, selected['role'],selected['run_kind'],(selected['workload'],selected['input_workload']),ledger=ledger,reader=reader)
        expected = max(GIB,(3*value['memory_peak_bytes']+1)//2)
    if expected != selected['claim_bytes']:
        raise ValueError('The staging claim differs from its selected evidence.')
    ledger = Path(ledger or env.get('ZESU_CANONICAL_LEDGER',memory.DEFAULT_LEDGER))
    key = memory.shell_key(marker)
    with memory.ledger_transaction(ledger)as data:
        data = copy.deepcopy(data)
    owner = data['shell_claim_owners'][key]; attestation = owner['guard_attestation']; actor=identity(os.getpid())
    if (actor != attestation['actor'] or owner['marker'] != str(Path(marker).absolute())
            or data['fixed_claims'].get(key) != selected['claim_bytes']
            or reader.claim(data,key).get('verified') is not True):
        raise ValueError('The staging supervisor lacks its exact guarded leaf.')
    argv=attestation['scope_exec_argv']; position=argv.index('scope-exec')
    if argv[position+1:] != [str(marker),'--',*command]:
        raise ValueError('The staging pre-exec command changed.')
    reader.ancestry(owner['owner']['pid'], selected['owner'])
    reader.guard_source(owner['guard_source']['path'],owner['guard_source']['sha256'])
    fence(Path(attestation['leaf']['scope']),reader,selected['physical_fence_bytes'])
    root_key=None;root_owner=None
    if selected['role']==ROLES[1]:
        candidate=selected['job']['policy']['claim_key']
        active=data['fixed_claims'].get(candidate,0)>0
        if active != (selected.get('canonical_root') is not None):
            raise ValueError('The staging descriptor changed its canonical root state.')
    if selected['role']==ROLES[1] and selected.get('canonical_root') is not None:
        root_key=candidate
        root_owner=data['entry_pilot_outside_owners'][root_key]
        if ({k:root_owner[k]for k in ('pid','startticks')}!=selected['owner']
                or data['fixed_claims'].get(root_key)!=selected['default_claim_bytes']
                or root_owner!=selected['canonical_root']):
            raise ValueError('The owned staging root identity changed.')
    return {'ledger':ledger,'reader':reader,'claim_key':key,'owner_record':owner,
        'scope_actor':actor,'scope':attestation['leaf'],'guard_source':owner['guard_source'],
        'context':reference,'role':selected['role'],'run_kind':selected['run_kind'],
        'root_claim_key':root_key,'root_owner':root_owner,'physical_fence_bytes':selected['physical_fence_bytes'],
        'staging_registry':registry_context(env,actor,reader)}


def entered(reference, command):
    import admission_memory as memory
    reader=memory.ScopeReader(); value=context(reference,reader)
    if command != payload(reference,value):
        raise ValueError('The staging child command changed.')
    marker=Path(os.environ['ZESU_OWNED_GUARD_TOKEN'])
    with memory.ledger_transaction(Path(os.environ.get('ZESU_CANONICAL_LEDGER',memory.DEFAULT_LEDGER)))as data:
        row=data['shell_claim_owners'][memory.shell_key(marker)]
        if data['fixed_claims'].get(memory.shell_key(marker)) != value['claim_bytes']:
            raise ValueError('The staging child claim changed.')
    reader.ancestry(os.getpid(),row['guard_attestation']['actor'])
    actual=next(line[3:]for line in Path('/proc/self/cgroup').read_text().splitlines()if line.startswith('0::'))
    if str(reader.root/actual.lstrip('/')) != row['guard_attestation']['leaf']['scope']:
        raise ValueError('The staging child left its dedicated leaf.')
    return value


def enter_prepare(script, arguments):
    if '--prepare-only' not in arguments or arguments[:1] in (['--run'],['--refresh-memory']):
        return
    command=[sys.executable,'-B',str(Path(script).resolve()),*arguments]
    if any(os.environ.get(key) for key in KEYS):
        entered({'path':os.environ[KEYS[0]],'sha256':os.environ[KEYS[1]]},command)
        return
    from harness_commit import pin, option
    harness=pin(option(arguments,'--harness-commit'))
    limit=int(os.environ.get('ZESU_MODULE_LIMIT_GIB',os.environ.get('ZESU_GATE_MODULE_LIMIT_GIB','16')))*GIB
    default=int(os.environ.get('ZESU_MODULE_CLAIM_BYTES',str(limit)))
    reference,value,env=create(ROLES[0],harness,command,default,limit)
    guard=str(Path(harness['root'])/'tools/resource_guard.sh')
    argv=[guard,'batch','public-prepare','--',guard,'scope','public-prepare',
          '--cpu','unlimited','--',*payload(reference,value)]
    os.execvpe(argv[0],argv,env)
    raise RuntimeError('The staging scope launcher returned.')


def stage(config, job, out):
    from entry_chain import save
    from memory_policy import environment as job_environment
    output=Path(out)
    configuration=Path(config['runtime_path'])
    raw=read_bound(binding(configuration))
    derived={key:config[key]for key in ('runtime_path','runtime_sha256')if key in config and key not in raw}
    if configuration_value(binding(configuration),derived) != config:
        raise ValueError('The staging configuration differs from its public runtime.')
    started=output/'STARTED.json'
    canonical_root=read_bound(binding(started))['owner'] if started.is_file() else None
    script=Path(config['harness']['root'])/'tools/block/harness/code/staging_peaks.py'
    command=[sys.executable,'-B',str(script),'--execute']
    from check_entry_outside import clean_environment
    reference,value,env=create(ROLES[1],config['harness'],command,job['claim_bytes'],
        job['physical_fence_bytes'],job=job,configuration=binding(configuration),output=str(output),environment=clean_environment(),
        derived=derived,canonical_root=canonical_root)
    env.update(job_environment(job['phase'],job['claim_bytes'],job=job))
    env['ZESU_MODULE_CLAIM_BYTES']=str(value['claim_bytes'])
    if 'ZESU_WRITER_MAX_COQC' in os.environ:
        env['ZESU_WRITER_MAX_COQC']=os.environ['ZESU_WRITER_MAX_COQC']
    guard=str(Path(config['harness']['root'])/'tools/resource_guard.sh')
    argv=[guard,'batch','entry-staging-'+job['key'],'--',guard,'scope','owned-staging',
          '--cpu','unlimited','--',*payload(reference,value)]
    save(output/'STAGING-LAUNCH.json',{'argv':argv,'owner':canonical_root,'context':reference})
    from controller_cleanup import launch
    child=launch(argv,env=env,start_new_session=True)
    save(output/'STAGING-PROCESS.json',identity(child.pid))
    status=child.wait()
    save(output/'STAGING-EXIT.json',{'context':reference,'returncode':status,'argv':argv})
    if status!=0:
        raise ValueError('The dedicated owned-staging payload failed with status '+str(status)+'.')
    runtime=read_bound(binding(output/'RUNTIME.json'))
    return runtime,Path(runtime['prepared_workspace'])


def authenticate_launch(reader, launch, owner, owner_args, out, canonical, amount=None):
    """Bind the pre-runtime leaf to its existing root without graph or Git work."""
    reference=launch['context']; value=reader.read(reference['path'])
    path=Path(reference['path'])
    if (hashlib.sha256(path.read_bytes()).hexdigest()!=reference['sha256']
            or value.get('schema')!=SCHEMA or value.get('role')!=ROLES[1]
            or value['owner']!={'pid':owner['pid'],'startticks':owner['startticks']}
            or value['configuration']!={'path':owner_args[3],'sha256':owner_args[4]}
            or value['output']!=str(out) or value['job']['key']!=owner['block']
            or value.get('canonical_root')!=owner
            or value['default_claim_bytes']!=canonical
            or (amount is not None and amount!=value['claim_bytes'])):
        raise ValueError('The early staging descriptor differs from its root.')
    root=Path(value['harness']['root'])
    if (value['producer']!=binding(root/'tools/block/harness/code/staging_peaks.py')
            or value['controller']!=binding(owner_args[2])):
        raise ValueError('The early staging producer source changed.')
    guard=root/'tools/resource_guard.sh'
    expected=[str(guard),'batch','entry-staging-'+owner['block'],'--',str(guard),
        'scope','owned-staging','--cpu','unlimited','--',*payload(reference,value)]
    if launch['owner']!=owner or launch['argv']!=expected:
        raise ValueError('The early staging command changed.')
    return expected,guard


def supervise(marker, command):
    start=begin(marker,command)
    def record(actor,code):
        try:finish(start,actor,code)
        except (KeyError,OSError,TypeError,ValueError)as error:
            print('resource guard: staging exit peak unavailable: '+str(error),file=sys.stderr)
    return run_payload(command,on_exit=record)


def main():
    if len(sys.argv)!=4 or sys.argv[1]!='--execute':
        raise ValueError('The staging worker requires one exact context.')
    reference={'path':sys.argv[2],'sha256':sys.argv[3]}
    value=entered(reference,[sys.executable,'-B',*sys.argv])
    from entry_chain_run import stage_job
    from phase_attribution import reference as attributed_runtime
    with attributed_runtime(value['configuration']):
        stage_job(configuration_value(value['configuration'],value.get('derived_configuration')),value['job'],Path(value['output']))
    return 0


if __name__=='__main__':raise SystemExit(main())
