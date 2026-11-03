"""Separate controller bookings from authenticated physical compiler bookings."""
from pathlib import Path
import json
import os
import sys
import uuid

from entry_chain import binding, read_bound

GIB = 1024 ** 3
SCHEMA = 'entry-chain.controller-booking.v1'
AUTHORITY = {'path': str(Path(__file__).resolve().parents[1] / 'policies' /
                         'CONTROLLER-PEAK-OBSERVATIONS.json'),
             'sha256': '5be79459f72d02889a05ad314a913ba2a68488bda8922ef962a9447662cd12dd'}
CONTROLLER_KEYS = ('ZESU_CONTROLLER_ROLE', 'ZESU_CONTROLLER_AUTHORITY_SHA256',
                   'ZESU_CONTROLLER_RUN_KIND', 'ZESU_CONTROLLER_BOOKING_JSON',
                   'ZESU_CONTROLLER_BOOKING_SHA256')
TOOLS = ('rocq_health', 'rocq_compile_file')


def controller_only(config, job=None):
    phase = job['phase'] if job is not None else config.get('phase')
    return (phase == 'prerequisites' and config.get('declarations_only') is True
            and config.get('control_session') is None and config.get('declaration_checks', []) == []
            and config.get('native_route') is None)


def descriptor(config, job=None):
    if not controller_only(config, job):
        return None
    reference = dict(AUTHORITY)
    if config.get('harness'):
        reference['path'] = str(Path(config['harness']['root']) /
            'tools/block/harness/policies/CONTROLLER-PEAK-OBSERVATIONS.json')
    authority = read_bound(reference)
    peaks = {row['pid']: row['memory.peak'] for row in authority['scopes']
             if row['pid'] in {740666, 756099, 762721}}
    if peaks != {740666: 14327521280, 756099: 16642785280, 762721: 6146703360}:
        raise ValueError('The approved historical MCP observations changed.')
    return {'schema': SCHEMA, 'authority': reference,
            'client_role': 'entry-chain-client', 'client_claim_bytes': GIB,
            'mcp_role': 'entry-pilot-mcp',
            'mcp_claim_bytes': max(GIB, (3 * max(peaks.values()) + 1) // 2),
            'allowed_tools': list(TOOLS),
            'qualification': 'Approved historical MCP-scope peaks, not completed aggregate measurements.'}


def run_kind(config, job=None):
    if not controller_only(config, job):
        raise ValueError('A controller booking requires a declaration-only run kind.')
    return 'declarations-dag' if config.get('declaration_dag') else 'declarations-serial'


def measured_descriptor(config, job=None):
    from role_peaks import last_peak, ROLES
    selected = descriptor(config, job)
    if selected is None:
        return None
    selected = dict(selected, run_kind=run_kind(config, job), exit_peaks={})
    for role, field in zip(ROLES, ('client_claim_bytes', 'mcp_claim_bytes')):
        observation = last_peak(role, selected['run_kind'])
        selected['exit_peaks'][role] = observation[0] if observation else None
        if observation:
            selected[field] = max(GIB, (3 * observation[1] + 1) // 2)
    return selected


def validate_booking(config, job, selected):
    """Revalidate pinned observations. Never replace them with newer records."""
    from role_peaks import recorded_peak, ROLES
    base = descriptor(config, job)
    if selected == base:
        return base
    if (base is None or not isinstance(selected, dict)
            or set(selected) != set(base) | {'run_kind', 'exit_peaks'}
            or selected['run_kind'] != run_kind(config, job)
            or not isinstance(selected['exit_peaks'], dict)
            or set(selected['exit_peaks']) != set(ROLES)):
        raise ValueError('The pinned controller booking changed its role or run kind.')
    expected = dict(base, run_kind=run_kind(config, job), exit_peaks=selected['exit_peaks'])
    for role, field in zip(ROLES, ('client_claim_bytes', 'mcp_claim_bytes')):
        reference = selected['exit_peaks'][role]
        if reference is not None:
            value = recorded_peak(reference, role, selected['run_kind'])
            expected[field] = max(GIB, (3 * value['memory_peak_bytes'] + 1) // 2)
    if selected != expected:
        raise ValueError('The pinned controller booking differs from its exit peak.')
    return selected


def _peak_context(runtime_reference, selected, role, environment, command=None):
    from role_peaks import CONTEXT_SCHEMA
    runtime = read_bound(runtime_reference)
    if selected['run_kind'] != run_kind(runtime):
        raise ValueError('The controller peak context differs from its runtime.')
    output = Path(runtime['job_output'])/'controller-bookings'
    output.mkdir(mode=0o700, exist_ok=True)
    path = output/(uuid.uuid4().hex+'.json')
    field = 'client_claim_bytes' if role == 'entry-chain-client' else 'mcp_claim_bytes'
    value = {'schema': CONTEXT_SCHEMA, 'runtime': runtime_reference, 'booking': selected,
             'role': role, 'run_kind': selected['run_kind'],
             'claim_bytes': selected[field], 'command': command}
    with open(path, 'x', opener=lambda name, flags: os.open(name, flags, 0o600)) as stream:
        json.dump(value, stream, sort_keys=True);stream.write('\n')
    environment.update(ZESU_CONTROLLER_RUN_KIND=selected['run_kind'],
                       ZESU_CONTROLLER_BOOKING_JSON=str(path),
                       ZESU_CONTROLLER_BOOKING_SHA256=binding(path)['sha256'])


def reset_controller(environment):
    result = dict(environment)
    for name in CONTROLLER_KEYS:
        result.pop(name, None)
    return result


def client_environment(config, job, environment):
    result = reset_controller(environment)
    selected = descriptor(config, job)
    path = Path(job['output'])/'RUNTIME.json' if job.get('output') else None
    if selected is not None and path is not None and path.is_file():
        runtime = read_bound(binding(path))
        if run_kind(config, job) != run_kind(runtime):
            raise ValueError('The client booking runtime changed its run kind.')
        selected = measured_descriptor(runtime)
        command = [sys.executable, '-B', config['job_controller']['path'], '--inside', job['output']]
        _peak_context(binding(path), selected, selected['client_role'], result, command)
    if selected is not None:
        result.update(ZESU_MODULE_CLAIM_BYTES=str(selected['client_claim_bytes']),
                      ZESU_CONTROLLER_ROLE=selected['client_role'],
                      ZESU_CONTROLLER_AUTHORITY_SHA256=selected['authority']['sha256'])
    return result, selected


def mcp_environment(runtime, environment):
    result = reset_controller(environment)
    selected = descriptor(runtime)
    if selected is not None and runtime.get('runtime_path') and runtime.get('runtime_sha256'):
        reference = {'path': runtime['runtime_path'], 'sha256': runtime['runtime_sha256']}
        selected = measured_descriptor(read_bound(reference))
        _peak_context(reference, selected, selected['mcp_role'], result)
    if selected is not None:
        result.update(ZESU_MODULE_CLAIM_BYTES=str(selected['mcp_claim_bytes']),
                      ZESU_CONTROLLER_ROLE=selected['mcp_role'],
                      ZESU_CONTROLLER_AUTHORITY_SHA256=selected['authority']['sha256'])
    else:
        # Native/control/PET-capable sessions retain the job's reviewed booking.
        from memory_policy import environment as job_environment
        policy = runtime.get('canonical_admission', {})
        if policy.get('memory_job') is not None:
            result.update(job_environment(runtime['phase'], policy['minimum_claim_bytes'],
                                          job=policy['memory_job']))
    return result, selected


def require_tool(selected, tool):
    if selected is not None and tool not in selected['allowed_tools']:
        raise ValueError('A controller-only MCP role cannot execute a proof command.')


def compiler_resources(runtime, config, workspace, output):
    from declaration_resources import weights
    from entry_chain import save
    modules = runtime['module_files']
    ordered = list(runtime['ordered_modules'])
    target = (runtime.get('target') or {}).get('block') or {}
    if target.get('module') in modules and target['module'] not in ordered:
        ordered.append(target['module'])
    profile = (runtime.get('declaration_dag') or {}).get('profile')
    if profile is None:
        rows = []
        for module in ordered:
            reference = config.get('object_imports', {}).get(module)
            if reference is not None and read_bound(reference).get('physical_result'):
                rows.append({'module': module, 'receipt': reference})
        if rows:
            path = Path(output) / 'COMPILER-MODULE-MEASUREMENTS.json'
            save(path, {'schema': 'entry-chain.declaration-resources.v1', 'modules': rows})
            profile = binding(path)
    selected = weights(ordered, modules, workspace, runtime['physical_compiler'],
                       runtime['physical_flags'], profile)
    return {'schema': 'entry-chain.compiler-scope-bookings.v1',
            'compiler': runtime['physical_compiler'], 'physical_flags': runtime['physical_flags'],
            'sources': {name: binding(Path(workspace) / modules[name]) for name in ordered},
            **selected}


def compiler_environment(runtime, source, environment):
    result = reset_controller(environment)
    amount = 16 * GIB
    selected = runtime.get('compiler_scope_bookings')
    if selected is not None:
        if (selected.get('schema') != 'entry-chain.compiler-scope-bookings.v1'
                or selected['compiler'] != runtime['physical_compiler']
                or selected['physical_flags'] != runtime['physical_flags']):
            raise ValueError('The physical compiler booking context changed.')
        owners = [name for name, row in selected['sources'].items() if row == source]
        if len(owners) > 1:
            raise ValueError('The physical compiler booking repeats its source owner.')
        if owners:
            name = owners[0]
            evidence = selected['evidence'][name]
            expected = (max(GIB, (3 * evidence['peak_bytes'] + 1) // 2)
                        if evidence['reason'] == 'completed_matching_measurement' else 16 * GIB)
            if selected['weights'][name] != expected:
                raise ValueError('The physical compiler booking formula changed.')
            amount = expected
    result['ZESU_MODULE_CLAIM_BYTES'] = str(amount)
    # An ambient profile must not override the authenticated runtime selection.
    result.pop('ZESU_MODULE_MEMORY_PROFILE', None)
    return result


def authenticate_client(config, controller, key, output, launch, amount, canonical):
    """Bind the smaller token to the exact reviewed controller command and job."""
    from harness_commit import check
    check(config['harness'])
    expected = Path(config['harness']['root']) / 'tools/block/harness/code/entry_chain_run.py'
    if Path(controller) != expected or config['job_controller'] != binding(expected):
        raise ValueError('The controller booking names another source command.')
    jobs = [row for row in config['jobs'] if row['key'] == key and row['output'] == str(output)]
    if len(jobs) != 1:
        raise ValueError('The controller booking names another job.')
    job = jobs[0]
    selected = validate_booking(config, job, launch.get('controller_booking'))
    if (selected is None or launch.get('controller_booking') != selected
            or amount != selected['client_claim_bytes']
            or job['claim_bytes'] != canonical or canonical < amount):
        raise ValueError('The early controller role or booking changed.')
    return True


def require_client(runtime, environment, *, kernel_driver=False):
    role = environment.get('ZESU_CONTROLLER_ROLE')
    if role is not None and (role != 'entry-chain-client' or descriptor(runtime) is None or kernel_driver):
        raise ValueError('A controller-only client cannot execute a proof or kernel driver.')
