"""Size only the released PORT36 verification continuation from its closed run."""
import hashlib
import json
from pathlib import Path


GIB = 1024 ** 3
BOOKING = 'completed_verification_peak'
CLAIM = 15 * GIB
FENCE = 64 * GIB
ROOT = Path('/home/cody/zesislar/_build/agents/worker-build-2')
PACKET = {'path': str(ROOT / 'PORT-v34-two-module-continuation-v1/FAILED-VERIFICATION-RESULT.json'),
          'sha256': '1d874268c3e698022c303974cb9e2e81073e57b5b50717f70f8e0fd158dc574b'}
CHECKS = {'path': str(ROOT / 'PORT-v34-verification-only-v1/CHECKS36-IMPORTS.json'),
          'sha256': 'cc4394daedffa084e6f099e95ef737c29c1791d231609448f6cdf3ba95774da9'}


def authenticate(reference):
    path = Path(reference['path'])
    with path.open('rb') as stream:
        digest = hashlib.file_digest(stream, 'sha256').hexdigest()
    if digest != reference['sha256']:
        raise ValueError('A completed verification binding changed.')
    return path


def read(reference):
    return json.loads(authenticate(reference).read_text())


def references(profile):
    if (set(profile) != {'schema', 'kind', 'sources', 'memory_booking', 'completed_verification_peak'} or
            profile['schema'] != 'scratch.admission-profile.v1' or
            profile['kind'] != 'focused_check' or profile['sources'] != [] or
            profile['memory_booking'] != BOOKING or profile['completed_verification_peak'] != PACKET):
        raise ValueError('The completed verification profile is not the released profile.')
    packet = read(PACKET)
    return [PACKET, CHECKS, packet['outer_runtime'], packet['inner_runtime'],
            packet['result'], packet['closure'], packet['release'], packet['calls']]


def historical(profile):
    for reference in references(profile):
        authenticate(reference)
    packet = read(PACKET)
    inner = read(packet['inner_runtime'])
    result = read(packet['result'])
    closure = read(packet['closure'])
    release = read(packet['release'])
    cpu = result['CPU']
    if (packet['READY_granted'] is not False or packet['checks_expected'] != 36 or
            inner['phase'] != 'prerequisites' or result['phase'] != 'prerequisites' or
            result['success'] is not False or result['returncode'] != 1 or
            result['status'] != 'infrastructure_failed' or result.get('resource_reason') or
            cpu != packet['CPU'] or cpu['aggregate_peak_bytes'] != 9710780416 or
            result['aggregate_peak_bytes'] != cpu['aggregate_peak_bytes'] or
            cpu['CPU_budget_enforced'] is not False or
            cpu['final_memory_accounting_available'] is not True or
            cpu['memory_events']['available'] is not True or
            any(cpu['memory_events']['counters'].get(key, 0) for key in
                ['max', 'oom', 'oom_kill', 'oom_group_kill'])):
        raise ValueError('The completed verification measurement is invalid.')
    if (closure['all_owned_actors_closed'] is not True or not closure['actors'] or
            any(row.get('ended') is not True for row in closure['actors']) or
            release['released'] is not True or release['bytes'] != 16 * GIB or
            release['claim_key'] != closure['claim_key'] or
            packet['claim_bytes_released'] != release['bytes'] or
            packet['aggregate_absent'] is not True or
            Path(packet['aggregate']['aggregate_path']).exists() or
            packet['final_binding_validation']['final_validation']['success'] is not True):
        raise ValueError('The completed verification lifecycle is incomplete.')
    directory = Path(inner['job_output'])
    for key, name in [('inner_runtime', 'RUNTIME.json'), ('result', 'RESULT.json'),
                      ('closure', 'CLOSURE.json'), ('release', 'RELEASE.json')]:
        if Path(packet[key]['path']) != directory / name:
            raise ValueError('The completed verification evidence leaves its job.')
    if cpu['memory_peak_source'] != packet['aggregate']['aggregate_path'] + '/memory.peak':
        raise ValueError('The completed verification peak names another aggregate.')
    # The release fixes 15 GiB; this is not a new generic rounding formula.
    if (3 * cpu['aggregate_peak_bytes'] + 1) // 2 > CLAIM:
        raise ValueError('The released claim does not cover the completed verification peak.')
    return inner


def normalized(flags, workspace):
    return [word.replace(str(workspace), '{workspace}') for word in flags]


def validate_context(profile, job, context, sources):
    inner = historical(profile)
    if (job['phase'] != 'prerequisites' or job.get('ordered_modules') != [] or
            job.get('declaration_dag_booking') or context.get('declarations_only') is not True or
            context.get('control_session') is not None or
            context.get('declaration_checks') != read(CHECKS) or
            context.get('target') != inner['target']['block'] or job.get('target') != context['target'] or
            context.get('compiler') != inner['physical_compiler'] or
            context.get('normalized_flags') != normalized(inner['physical_flags'],
                                                        Path(inner['job_output']) / 'workspace')):
        raise ValueError('The verification continuation names another subject, check set, or compiler.')
    authenticate(context['compiler'])
    expected = {row['module']: row['source']['sha256'] for row in inner['declared_outputs']}
    expected[inner['target']['block']['module']] = inner['target']['block']['source_sha256']
    if len(sources) != len(expected) or {row['module']: row['sha256'] for row in sources} != expected:
        raise ValueError('The verification continuation changed a bound source.')
    for row in sources:
        authenticate(row)
    return CLAIM


def workload(reference, profile, job, config):
    if config.get('declarations_only') is not True:
        raise ValueError('The completed verification route requires declaration-only execution.')
    if job['phase'] == 'native' and job.get('ordered_modules', []) == [] and job.get('native_route') is None:
        return None
    inner = historical(profile)
    modules = [row['module'] for row in inner['declared_outputs']] + [inner['target']['block']['module']]
    root = Path(config['prepared_workspace'])
    sources = []
    for module in modules:
        path = root / config['proof_runtime']['module_files'][module]
        with path.open('rb') as stream:
            digest = hashlib.file_digest(stream, 'sha256').hexdigest()
        sources.append({'module': module, 'path': str(path), 'sha256': digest})
    context = {'declarations_only': config['declarations_only'],
               'control_session': config.get('control_session'),
               'declaration_checks': config.get('declaration_checks'), 'target': job.get('target'),
               'compiler': config['effective_compiler_version']['compiler'],
               'normalized_flags': normalized(config['physical_flags'], root)}
    validate_context(profile, job, context, sources)
    return {'kind': 'focused_check', 'profile': reference, 'owned_sources': sources,
            'declarations_only': True, 'verification_context': context}


def claim(workload, job):
    return validate_context(read(workload['profile']), job, workload['verification_context'],
                            workload['owned_sources'])
