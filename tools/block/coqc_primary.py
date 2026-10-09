#!/usr/bin/env python3
"""Run a guarded native primary through coqc when Pet cannot start.

The recorder observes active goals. Other native groups remain unavailable.
A compiler exit alone never establishes a designed boundary proof.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import resource
import shutil
import subprocess
import sys
import time

import chain_goals
import coqc_certificate


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def budget_policy(seconds=300, cpu_seconds=None, *, memory_gib=6, entry_pc=None, diagnostic_probe=False):
    if diagnostic_probe:
        if cpu_seconds is not None or memory_gib != 64:
            raise ValueError("A diagnostic probe requires unlimited CPU and 64 GiB")
        return {"kind": "probe", "cpu_seconds": None, "wall_seconds": None,
                "memory_kib": 64*1024*1024, "optimization_debt": "issue#10"}
    if memory_gib not in (6, 12):
        raise ValueError('The memory budget must be six or twelve GiB')
    if memory_gib == 12 and (entry_pc != '0x800d698c' or cpu_seconds is None):
        raise ValueError('The twelve-GiB exception applies only to completion entry0x800d698c')
    if cpu_seconds is not None:
        maximum = 2400 if entry_pc in ('0x800d6a24', '0x800d6ac4') else 1200
        if not isinstance(cpu_seconds, int) or not 0 < cpu_seconds <= maximum:
            raise ValueError('The CPU budget exceeds the authorized completion entry budget')
        return {'kind': 'cpu', 'cpu_seconds': cpu_seconds, 'wall_seconds': None,
                'memory_kib': memory_gib*1024*1024,
                **({'completion_entry': entry_pc, 'optimization_debt': 'issue#10'}
                   if cpu_seconds > 1200 or memory_gib > 6 else {})}
    if not 0 < seconds <= 300:
        raise ValueError('The primary budget must be between one and 300 seconds')
    return {'kind': 'wall', 'cpu_seconds': None, 'wall_seconds': seconds,
            'memory_kib': 6*1024*1024}


def completion_environment(policy):
    if policy['kind'] == 'probe':
        return {'ZESU_DIAGNOSTIC_PROBE': '1', 'ZESU_PROBE_ISSUE': '10',
                'ZESU_PRIMARY_CPU_LIMIT': 'none', 'ZESU_PROOF_CPU_LIMIT': 'unlimited',
                'ZESU_PRIMARY_WALL_LIMIT': 'none', 'ZESU_SCRATCH_WALL_SECONDS': 'none',
                'ZESU_PRIMARY_MEMORY_GIB': '64', 'ZESU_SCRATCH_MEMORY_GIB': '64',
                'ZESU_MODULE_LIMIT_GIB': '64'}
    return {'ZESU_DIAGNOSTIC_PROBE': '0', 'ZESU_PROBE_ISSUE': '',
            'ZESU_PRIMARY_CPU_LIMIT': str(policy['cpu_seconds'] or 0),
            'ZESU_PRIMARY_MEMORY_GIB': str(policy['memory_kib']//(1024*1024)),
            'ZESU_SCRATCH_MEMORY_GIB': str(policy['memory_kib']//(1024*1024)),
            'ZESU_COMPLETION_ENTRY': policy.get('completion_entry', ''),
            'ZESU_PRIMARY_WALL_LIMIT': str(policy['wall_seconds'] or 'none'),
            'ZESU_SCRATCH_WALL_SECONDS': str(policy['wall_seconds'] or 'none'),
            **({'ZESU_PROOF_CPU_LIMIT': str(policy['cpu_seconds'])}
               if policy['cpu_seconds'] else {})}


def instrument(rendered, seconds=300, *, cpu_seconds=None, memory_gib=6, diagnostic_probe=False):
    policy = budget_policy(seconds, cpu_seconds, memory_gib=memory_gib, entry_pc=rendered['entry_pc'], diagnostic_probe=diagnostic_probe)
    source = rendered['source']
    marker = 'Lemma ' + rendered['lemma']
    start = source.index(marker)
    end = source.index('\nProof.\n', start)
    statement = source[start:end]
    if (rendered.get('scope') != 'unproved native designed boundary' or
            not rendered.get('entry_pc') or not rendered.get('entry_definition') or
            hashlib.sha256(statement.encode()).hexdigest() != rendered.get('statement_sha256') or
            not re.search(r'\binstr_body\s+' + re.escape(rendered['entry_pc']) + r'\b', statement)):
        raise ValueError('The native boundary signature is unavailable')
    body, tail = source[end + len('\nProof.\n'):].split('\nQed.', 1)
    if body.strip() != 'try zesu_block.':
        raise ValueError('The primary body must contain only the unchanged tactic')
    prefix = source[:start]
    if 'Ltac chain_print_goal ' not in prefix:
        prefix += chain_goals.RECORDER + '\n'
    prefix += statement
    tactic = 'try zesu_block.' if policy['kind'] in ('cpu', 'probe') else f'Timeout {seconds} try zesu_block.'
    instrumented = (prefix + '\nProof.\nidtac \"COQC-PRIMARY-BEGIN\".\n' + tactic + '\n'
                    'all: (chain_print_goal "active"; idtac "CHAIN-GOAL-END").\n'
                    'Show Existentials.\nQed.' + tail)
    if 'Print Assumptions ' + rendered['lemma'] + '.' not in tail:
        instrumented += '\nPrint Assumptions ' + rendered['lemma'] + '.\n'
    return instrumented


def assumptions_result(output, lemma):
    # This statement runs only after the native Qed command succeeds.
    if 'Axioms:' in output or 'Assumptions:' in output:
        return {'verified': False, 'reason': 'The compiled theorem has assumptions'}
    if 'Closed under the global context' not in output:
        return {'verified': False, 'reason': 'The compiler returned no assumption certificate'}
    return {'verified': True, 'assumptions': [], 'method': 'In-module Print Assumptions ' + lemma}


def decode_active(output):
    """Decode complete conclusion-delimited records without changing raw bytes."""
    starts = list(re.finditer(r'CHAIN-GOAL-BEGIN\s+"?(active|shelved)"?\b', output))
    records = []
    for index, start in enumerate(starts):
        end = starts[index+1].start() if index+1 < len(starts) else len(output)
        segment = output[start.start():end]
        conclusions = list(re.finditer(r'"?CHAIN-GOAL-CONCLUSION"?\s+.*?\s*CHAIN-FIELD-END', segment, re.S))
        if len(conclusions) != 1:
            raise ValueError('The printed goal lacks one terminated conclusion')
        # A Coq all-selector can emit only one final END marker. The conclusion
        # terminator still defines each complete record. Never recover a partial field.
        normalized = segment[:conclusions[0].end()] + '\nCHAIN-GOAL-END\n'
        records.extend(chain_goals.parse_goals(normalized, phase='active', allow_local_definitions=True))
    return records


def diagnostic_active(output):
    """A failed import or interrupted primary has no returned goal group."""
    if not re.search(r'^COQC-PRIMARY-BEGIN\s*$', output, re.M):
        return None
    if 'CHAIN-GOAL-BEGIN' not in output and '[Show~Existentials.]' not in output:
        return None
    return decode_active(output)


def probe_scope_path(pid):
    cgroup = next(line.split(':', 2)[2] for line in
                  Path(f'/proc/{pid}/cgroup').read_text().splitlines()
                  if line.startswith('0::'))
    scope = Path('/sys/fs/cgroup') / cgroup.lstrip('/')
    return scope


def probe_scope_limits(pid):
    scope = probe_scope_path(pid)
    return {'memory_max_bytes': int((scope/'memory.max').read_text()),
            'memory_swap_max_bytes': int((scope/'memory.swap.max').read_text())}


def probe_memory_events(pid):
    return dict((key, int(value)) for key, value in
                (line.split() for line in (probe_scope_path(pid)/'memory.events').read_text().splitlines()))


def compiler_run(arguments):
    record = Path(os.environ['ZESU_PRIMARY_COMPILER_RECORD'])
    command = ['/home/cody/islaris/_opam/bin/coqc', '-time', *arguments]
    started = time.monotonic()
    probe = os.environ.get('ZESU_DIAGNOSTIC_PROBE') == '1'
    cpu_text = os.environ.get('ZESU_PRIMARY_CPU_LIMIT', '0')
    if probe and (cpu_text != 'none' or
            os.environ.get('ZESU_PRIMARY_WALL_LIMIT') != 'none' or
            os.environ.get('ZESU_PRIMARY_MEMORY_GIB') != '64' or
            os.environ.get('ZESU_PROBE_ISSUE') != '10' or os.environ.get('ZESU_IN_GATE')):
        raise ValueError('A diagnostic probe requires issue10, 64 GiB, and unlimited CPU and wall time')
    if probe and probe_scope_limits(os.getpid()) != {
            'memory_max_bytes': 64*1024**3, 'memory_swap_max_bytes': 0}:
        raise ValueError('The diagnostic scope limits differ from the probe policy')
    cpu_limit = None if probe else int(cpu_text) or None
    wall_text = os.environ.get('ZESU_PRIMARY_WALL_LIMIT', '300')
    wall_limit = None if wall_text == 'none' else float(wall_text)
    memory_limit = int(os.environ.get('ZESU_PRIMARY_MEMORY_GIB', '6'))*1024*1024
    before_memory_events = probe_memory_events(os.getpid()) if probe else None
    after_memory_events = None
    before_cpu = resource.getrusage(resource.RUSAGE_CHILDREN)
    def set_cpu_limit():
        if probe:
            resource.setrlimit(resource.RLIMIT_CPU, (resource.RLIM_INFINITY, resource.RLIM_INFINITY))
        elif cpu_limit:
            resource.setrlimit(resource.RLIMIT_CPU, (cpu_limit, cpu_limit))
    process = subprocess.Popen(command, preexec_fn=set_cpu_limit if probe or cpu_limit else None)
    actual_cpu_limits = None
    actual_scope_limits = None
    policy_error = None
    telemetry_errors = {'count': 0, 'first': None, 'last': None}
    cpu_used = 0.0
    peak, limit, saved = 0, None, started
    def save(code=None, compiled=None):
        value = {'compiler_pid': process.pid, 'command': command, 'cwd': os.getcwd(),
            'elapsed_seconds': time.monotonic()-started, 'peak_rss_kib': peak,
            'exit_code': code, 'limit': limit, 'compiled_object': compiled,
            'measurement_complete': code is not None,
            'cpu_seconds': cpu_used,
            'actual_cpu_limits': actual_cpu_limits, 'actual_scope_limits': actual_scope_limits,
            'policy_error': policy_error,
            'telemetry_errors': telemetry_errors,
            'scope_memory_events_before': before_memory_events,
            'scope_memory_events_after': after_memory_events,
            'limits': {'module_seconds': wall_limit, 'cpu_seconds': cpu_limit, 'rss_kib': memory_limit}}
        temporary = record.with_suffix('.tmp')
        temporary.write_text(json.dumps(value, indent=2)+'\n')
        temporary.replace(record)
    save()
    while process.poll() is None:
        if probe and actual_cpu_limits is None:
            try:
                soft, hard = resource.prlimit(process.pid, resource.RLIMIT_CPU)
                actual_cpu_limits = {'soft': None if soft == resource.RLIM_INFINITY else soft,
                                     'hard': None if hard == resource.RLIM_INFINITY else hard}
                actual_scope_limits = probe_scope_limits(process.pid)
                if (actual_cpu_limits != {'soft': None, 'hard': None} or
                        actual_scope_limits != {'memory_max_bytes': 64*1024**3, 'memory_swap_max_bytes': 0}):
                    raise ValueError('The diagnostic child limits differ from the probe policy')
            except (OSError, ValueError, StopIteration) as error:
                if isinstance(error, (FileNotFoundError, ProcessLookupError, StopIteration)):
                    policy_error = 'The live diagnostic child limits are unavailable'
                else:
                    policy_error = str(error)
        try:
            peak = max(peak, next(int(line.split()[1]) for line in
                Path(f'/proc/{process.pid}/status').read_text().splitlines() if line.startswith('VmRSS:')))
            fields = Path(f'/proc/{process.pid}/stat').read_text().rsplit(')', 1)[1].split()
            cpu_used = (int(fields[11]) + int(fields[12])) / os.sysconf('SC_CLK_TCK')
        except (OSError, ValueError, StopIteration) as error:
            # A proc entry or VmRSS can disappear while the child exits.
            sample = {'elapsed_seconds': time.monotonic()-started,
                      'error_type': type(error).__name__}
            telemetry_errors['count'] += 1
            if telemetry_errors['first'] is None:
                telemetry_errors['first'] = sample
            telemetry_errors['last'] = sample
        if policy_error is not None:
            limit = 'policy'
            process.terminate()
            try:
                process.wait(timeout=2)
            except subprocess.TimeoutExpired:
                process.kill()
                process.wait()
            break
        if time.monotonic()-saved >= 1:
            save()
            saved = time.monotonic()
        wall_exceeded = wall_limit is not None and time.monotonic()-started > wall_limit
        if wall_exceeded or peak > memory_limit:
            limit = 'time' if wall_exceeded else 'memory'
            process.terminate()
            try:
                process.wait(timeout=2)
            except subprocess.TimeoutExpired:
                process.kill()
                process.wait()
            break
        time.sleep(0.025)
    code = process.wait()
    if probe:
        after_memory_events = probe_memory_events(os.getpid())
        if after_memory_events.get('oom_kill', 0) > before_memory_events.get('oom_kill', 0):
            limit = 'memory'
    after_cpu = resource.getrusage(resource.RUSAGE_CHILDREN)
    cpu_used = after_cpu.ru_utime + after_cpu.ru_stime - before_cpu.ru_utime - before_cpu.ru_stime
    if cpu_limit and code in (-9, -24) and cpu_used >= cpu_limit - 1:
        limit = 'cpu'
    peak = max(peak, resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss)
    compiled = None
    if code == 0 and limit is None and '-o' in arguments:
        generated = Path(arguments[arguments.index('-o')+1])
        if generated.exists():
            retained = Path(os.environ['ZESU_PRIMARY_COMPILED_OBJECT'])
            shutil.copyfile(generated, retained)
            compiled = {'path': str(retained), 'sha256': digest(retained)}
    save(code, compiled)
    return code if limit is None else 1


def compile_source(path, out, build, *, policy):
    path, out, build = Path(path).resolve(), Path(out).resolve(), Path(build).resolve()
    out.mkdir(parents=True, exist_ok=True)
    if (out/'compiler.json').exists() or (out/'compiler.log').exists():
        raise ValueError('An existing compiler attempt must not be repeated')
    wrapper = out/'compiler-wrapper'
    wrapper.write_text('#!/bin/sh\nexec ' + sys.executable + ' ' + str(Path(__file__).resolve()) + ' --compiler "$@"\n')
    wrapper.chmod(0o755)
    compiler_record = out/'compiler.json'
    tool = Path(__file__).resolve().parents[1]/'coqc_scratch.sh'
    command = [str(tool), str(path), str(build)]
    started = time.monotonic()
    done = subprocess.run(command, capture_output=True, text=True, env={**os.environ, **completion_environment(policy),
        'ZESU_SCRATCH_COQC_BINARY': str(wrapper), 'ZESU_PRIMARY_COMPILER_RECORD': str(compiler_record),
        'ZESU_PRIMARY_COMPILED_OBJECT': str(out/(path.stem + '.vo'))})
    output = done.stdout + done.stderr
    log = out/'compiler.log'
    log.write_text(output)
    compiler = json.loads(compiler_record.read_text()) if compiler_record.exists() else None
    return done, output, log, compiler, time.monotonic()-started


def run_primary(rendered, out, build, *, inherited_debts, seconds=300, cpu_seconds=None, memory_gib=6, diagnostic_probe=False):
    if not isinstance(inherited_debts, dict):
        raise ValueError('Inherited debts must be explicit')
    out, build = Path(out).resolve(), Path(build).resolve()
    out.mkdir(parents=True, exist_ok=True)
    if (out/'evidence.json').exists():
        raise ValueError('An existing native attempt must be reused, not repeated')
    path = out/'Boundary.v'
    policy = budget_policy(seconds, cpu_seconds, memory_gib=memory_gib, entry_pc=rendered['entry_pc'], diagnostic_probe=diagnostic_probe)
    source = instrument(rendered, seconds, cpu_seconds=cpu_seconds, memory_gib=memory_gib, diagnostic_probe=diagnostic_probe)
    path.write_text(source)
    done, output, log, compiler, total_wall = compile_source(path, out, build, policy=policy)
    capture_error = None
    try:
        active = diagnostic_active(output)
    except ValueError as error:
        active, capture_error = None, str(error)
    assumption = assumptions_result(output, rendered['lemma'])
    command_times = [(line, float(value)) for line, value in
        re.findall(r'^(Chars .*?) ([0-9.]+) secs ', output, re.M)]
    primary_indices = [index for index, (line, _) in enumerate(command_times)
                       if 'zesu_block' in line]
    primary_time = sum(command_times[index][1] for index in primary_indices) if primary_indices else None
    setup_time = sum(value for _, value in command_times[:primary_indices[0]]) if primary_indices else None
    compiled = bool(done.returncode == 0 and compiler and compiler['exit_code'] == 0 and
                    compiler['limit'] is None and compiler['compiled_object'])
    outcome = ('native-qed-certificate' if compiled and assumption['verified'] else
               'limit-stop' if (compiler and compiler['limit']) or
                   'proof limit exceeded:' in output else
               'native-residual' if active or ('COQC-PRIMARY-BEGIN' in output and
                   'Attempt to save an incomplete proof' in output) else 'coqc-primary-unavailable')
    result = {'source': str(path), 'source_sha256': digest(path),
        'original_source_sha256': hashlib.sha256(rendered['source'].encode()).hexdigest(),
        'statement_sha256': rendered['statement_sha256'], 'entry_pc': rendered['entry_pc'],
        'entry_definition': rendered['entry_definition'], 'successors': rendered['successors'],
        'terminal_scope': rendered.get('terminal_scope'), 'scope': rendered['scope'],
        'setup_path': 'approved coqc primary fallback; no Pet start', 'scratch_command': done.args,
        'primary_tactic': 'try zesu_block.', 'primary_timeout': policy['wall_seconds'],
        'proof_budget': policy,
        'budget_policy': ('The diagnostic probe has unlimited CPU and no wall cutoff; issue#10 records its 64 GiB cap.'
                          if diagnostic_probe else
                          ('The compiler CPU limit applies to the whole module; no wall cutoff applies.'
                           if cpu_seconds else 'The tactic wall limit and the outer module limit include recording.')),
        'primary_tactic_entered': 'COQC-PRIMARY-BEGIN' in output,
        'compiler': compiler, 'total_wall_seconds': total_wall,
        'coq_command_setup_seconds': setup_time, 'coq_primary_command_seconds': primary_time,
        'command_timing_scope': 'Coqc -time command elapsed values; guard wait and compiler startup are not included',
        'guard_wait_seconds': None, 'log': str(log), 'log_sha256': digest(log),
        'active_goals': active, 'capture_error': capture_error,
        'capture_delimiter_policy': 'Each decoded record ends at its complete conclusion field; raw bytes remain unchanged',
        'group_coverage': {'goals': 'Coq pretty-printed active goals' if active is not None else 'unavailable',
                          'stack': 'unavailable', 'shelf': 'unavailable', 'given_up': 'unavailable'},
        'inherited_debts': inherited_debts, 'assumption_verification': assumption,
        'native_qed_compiled': compiled, 'block_closed': False, 'contract_closed': False,
        'outcome': outcome}
    if digest(path) != hashlib.sha256(source.encode()).hexdigest():
        raise ValueError('The instrumented source changed during primary execution')
    result['block_closed'] = coqc_certificate.native_closed(result, rendered)
    if result['block_closed']:
        result['outcome'] = 'native-boundary-closed'
    result['closure_policy'] = 'Exact kernel-accepted Qed, empty assumptions, and no inherited debts certify the native boundary. Pet groups remain unavailable diagnostics.'
    (out/'evidence.json').write_text(json.dumps(result, indent=2)+'\n')
    return result


if __name__ == '__main__':
    if sys.argv[1:2] == ['--compiler']:
        raise SystemExit(compiler_run(sys.argv[2:]))
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--compile', type=Path, required=True)
    parser.add_argument('--build-dir', type=Path, required=True)
    parser.add_argument('--out', type=Path, required=True)
    parser.add_argument('--cpu-seconds', type=int)
    parser.add_argument('--diagnostic-probe', action='store_true', help='Issue10 probe: 64 GiB, unlimited CPU, no wall limit')
    parser.add_argument('--memory-gib', type=int, default=6)
    parser.add_argument('--entry-pc', help='Required for an authorized module exception')
    args = parser.parse_args()
    if not args.diagnostic_probe and args.cpu_seconds is None:
        parser.error('--cpu-seconds is required outside the diagnostic probe policy')
    policy = budget_policy(cpu_seconds=args.cpu_seconds, memory_gib=args.memory_gib,
                           entry_pc=args.entry_pc, diagnostic_probe=args.diagnostic_probe)
    args.out.mkdir(parents=True, exist_ok=True)
    retained = args.out / args.compile.name
    original_hash = digest(args.compile)
    if retained.resolve() != args.compile.resolve():
        shutil.copyfile(args.compile, retained)
    done, output, log, compiler, wall = compile_source(retained, args.out, args.build_dir, policy=policy)
    if digest(retained) != original_hash:
        raise ValueError('The compile source changed during execution')
    result = {'source': str(retained.resolve()), 'source_sha256': original_hash,
              'compiler': compiler, 'proof_budget': policy, 'total_wall_seconds': wall,
              'log': str(log), 'log_sha256': digest(log), 'exit_code': done.returncode,
              'block_closed': False, 'contract_closed': False,
              'scope': 'generic module compilation; no native closure certification'}
    report = args.out/'compile-evidence.json'
    report.write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps({'report': str(report), 'sha256': digest(report), 'exit_code': done.returncode}))
    raise SystemExit(done.returncode)
