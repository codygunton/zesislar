"""Profile only the canonical PORT cases accepted by the shared policy."""
from pathlib import Path
import hashlib
import json
import shutil
import time

from perf_measure import prepare
from instruction_checkpoints import Counter
from port_native_policy import PERF, port_case


def profile_launcher(memory_job, row, workspace, output, launcher):
    case = port_case(memory_job)
    if case is None:
        return launcher, None
    target = row.get('block', {})
    if any(target.get(key) != case[key] for key in ('module', 'statement_sha256')):
        raise ValueError('The profiling target differs from the authorized PORT target.')
    try:
        pinned = Path(PERF['path'])
        if hashlib.sha256(pinned.read_bytes()).hexdigest() != PERF['sha256']:
            raise ValueError('The pinned perf executable changed.')
        measurement = prepare(launcher, Path(output) / 'instruction-profile', cwd=workspace)
        selected = Path(measurement['command'][0])
        if (selected.resolve() != pinned.resolve()
                or hashlib.sha256(selected.read_bytes()).hexdigest() != PERF['sha256']):
            raise ValueError('The selected perf executable differs from the pinned executable.')
        position = measurement['command'].index('--')
        measurement['command'][position:position] = ['--interval-print', '1000']
        measurement['interval_ms'] = 1000
        measurement['port_case'] = case
        measurement['perf_executable'] = dict(PERF)
        (Path(output) / 'instruction-profile/PROFILE-ACTIVE.json').write_text(
            json.dumps(dict(block=case['block'], case=case, interval_ms=1000)) + '\n')
        return measurement['command'], measurement
    except (OSError, ValueError, TypeError, KeyError) as error:
        # Preserve the original launcher when telemetry preparation fails.
        failure = dict(case=case, status='unavailable', failure='profile_preparation_failed',
                       detail=str(error), instruction_measurement_complete=False,
                       search_only=False, cache_status='Preparation failed; partial cache removal is possible.')
        try:
            directory = Path(output) / 'instruction-profile'
            directory.mkdir(parents=True, exist_ok=True)
            (directory / 'PROFILE-UNAVAILABLE.json').write_text(json.dumps(failure) + '\n')
            (Path(output) / 'INSTRUCTION-PROFILE.json').write_text(json.dumps(failure, indent=2) + '\n')
        except OSError:
            pass
        return launcher, None


def unavailable_profile(case, output, detail):
    failure = dict(case=case, status='unavailable', failure='profile_preparation_failed',
                   detail=str(detail), instruction_measurement_complete=False, search_only=False)
    try:
        directory = Path(output) / 'instruction-profile'
        directory.mkdir(parents=True, exist_ok=True)
        (directory / 'PROFILE-UNAVAILABLE.json').write_text(json.dumps(failure) + '\n')
        (Path(output) / 'INSTRUCTION-PROFILE.json').write_text(json.dumps(failure) + '\n')
    except OSError:
        pass


def prepare_launch(memory_job, row, workspace, output, launcher, environment):
    """Select once before collection. Never execute perf or the workload here."""
    import collector
    from entry_chain import binding
    case = port_case(memory_job)
    selected, measurement = profile_launcher(memory_job, row, workspace, output, launcher)
    inputs, resolution = [], []
    if measurement is not None:
        try:
            resolved = shutil.which('perf', path=environment['PATH'])
            if resolved is None or Path(resolved).resolve() != Path(selected[0]).resolve():
                raise ValueError('The typed PATH selects another perf executable.')
            policy = {'ldd': binding('/usr/bin/ldd'), 'optional_missing_edges': []}
            inputs.append(policy['ldd'])
            pending, seen = [Path(selected[0])], set()
            while pending:
                path = pending.pop(0)
                if path.resolve() in seen:
                    continue
                seen.add(path.resolve())
                inputs.append(binding(path))
                inspected = collector.libraries(path, policy, environment, str(workspace))
                if inspected['unresolved_edges']:
                    raise ValueError('The selected perf executable has an unresolved loader edge.')
                resolution.append(dict(file=binding(path), resolution=inspected))
                pending.extend(Path(item['path']) for item in inspected['ordered_libraries'])
        except (OSError, ValueError, TypeError, KeyError) as error:
            unavailable_profile(case, output, error)
            selected, measurement, inputs, resolution = launcher, None, [], []
    return dict(schema='port.checked-mcp-launch.v1', base_argv=list(launcher),
                argv=list(selected), workspace=str(workspace), output=str(output), case=case,
                measurement=measurement, executable_inputs=inputs, library_resolution=resolution,
                status='profiled' if measurement is not None else 'unprofiled')


def checked_launcher(memory_job, row, workspace, output, launcher, directory):
    """Consume the PHASE2-checked selection. Do not select or prepare again."""
    from entry_chain import check_bindings, read_bound, strict_loads
    directory = Path(directory)
    if directory.resolve() != (Path(output).parent / 'prospective').resolve():
        raise ValueError('The profiling transport leaves its exact owned attempt.')
    boundary = strict_loads((directory / 'ACTUAL-BOUNDARY.json').read_text())
    selected = boundary['mcp_launch']
    if Path(selected['path']).resolve() != (directory / 'MCP-LAUNCH.json').resolve():
        raise ValueError('The profiling transport names another selection file.')
    plan = read_bound(selected)
    report = read_bound(boundary['phase2'])
    if report.get('native_profile_transport') != selected:
        raise ValueError('The profiling transport differs from the PHASE2 report.')
    case = port_case(memory_job)
    if (plan.get('schema') != 'port.checked-mcp-launch.v1' or plan.get('case') != case
            or plan.get('workspace') != str(workspace) or plan.get('output') != str(output)
            or plan.get('base_argv') != list(launcher)):
        raise ValueError('The selected profiling command names another native context.')
    target = row.get('block', {})
    if case is not None and any(target.get(key) != case[key] for key in ('module', 'statement_sha256')):
        raise ValueError('The selected profiling target differs from the authorized PORT target.')
    vectors = [item for item in report['input']['recipe']['configuration']['execution_vectors']
               if item['role'] == 'mcp']
    if len(vectors) != 1 or vectors[0]['cwd']['value'] != str(workspace):
        raise ValueError('The selected profiling command has no exact typed execution vector.')
    values = vectors[0]['argv']
    if any(item['kind'] not in {'literal', 'path'} for item in values):
        raise ValueError('The selected profiling vector contains an unsupported transport value.')
    if [item['value'] for item in values] != plan['argv']:
        raise ValueError('The selected profiling argv differs from the typed execution vector.')
    measurement = plan['measurement']
    if measurement is None:
        if plan['status'] != 'unprofiled' or plan['argv'] != list(launcher) or plan['executable_inputs']:
            raise ValueError('The unprofiled selection changed the original MCP command.')
    else:
        if (case is None or plan['status'] != 'profiled'
                or measurement['command'] != plan['argv'] or measurement['workload_command'] != list(launcher)
                or measurement['cwd'] != str(workspace) or measurement['port_case'] != case
                or measurement['perf_executable'] != PERF
                or measurement['perf_stat'] != str(Path(output) / 'instruction-profile/perf-stat.csv')
                or PERF not in plan['executable_inputs']):
            raise ValueError('The profiled selection has another executable, output, or command.')
        check_bindings(plan['executable_inputs'])
    return plan['argv'], measurement


def complete_profile(measurement, output):
    if measurement is None or measurement.get('port_case') is None:
        return
    try:
        counter = Counter(measurement['perf_stat'])
        path = Path(measurement['perf_stat'])
        counter.poll(time.time_ns())
        while (not counter.failure and path.exists()
               and counter.offset < path.stat().st_size):
            counter.poll(time.time_ns())
        if counter.partial:
            counter.failure = 'incomplete_counter_line'
        snapshot = counter.snapshot()
        result = dict(measurement, counter=snapshot, interval_records=counter.records,
                      status='measured' if snapshot['instructions'] is not None else 'unavailable',
                      instruction_measurement_complete=snapshot['instructions'] is not None,
                      perf_stat_sha256=(hashlib.sha256(path.read_bytes()).hexdigest()
                                        if path.exists() else None))
    except (OSError, ValueError, TypeError):
        result = dict(measurement, status='unavailable',
                      instruction_measurement_complete=False)
    result['scope'] = 'MCP launcher and descendants over the full MCP session.'
    result['search_only'] = False
    result['tactic_cost_breakdown'] = False
    try:
        (Path(output) / 'INSTRUCTION-PROFILE.json').write_text(
            json.dumps(result, indent=2) + '\n')
    except OSError:
        # A report failure cannot change an existing proof or guard result.
        pass
