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


def instrument(rendered, seconds=300):
    if not 0 < seconds <= 300:
        raise ValueError('The primary budget must be between one and300seconds')
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
    instrumented = (prefix + '\nProof.\nidtac \"COQC-PRIMARY-BEGIN\".\n' + f'Timeout {seconds} try zesu_block.\n'
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
        records.extend(chain_goals.parse_goals(normalized, phase='active'))
    return records


def compiler_run(arguments):
    record = Path(os.environ['ZESU_PRIMARY_COMPILER_RECORD'])
    command = ['/home/cody/islaris/_opam/bin/coqc', '-time', *arguments]
    started = time.monotonic()
    process = subprocess.Popen(command)
    peak, limit, saved = 0, None, started
    def save(code=None, compiled=None):
        value = {'compiler_pid': process.pid, 'command': command, 'cwd': os.getcwd(),
            'elapsed_seconds': time.monotonic()-started, 'peak_rss_kib': peak,
            'exit_code': code, 'limit': limit, 'compiled_object': compiled,
            'measurement_complete': code is not None,
            'limits': {'module_seconds': 300, 'rss_kib': 6*1024*1024}}
        temporary = record.with_suffix('.tmp')
        temporary.write_text(json.dumps(value, indent=2)+'\n')
        temporary.replace(record)
    save()
    while process.poll() is None:
        try:
            peak = max(peak, next(int(line.split()[1]) for line in
                Path(f'/proc/{process.pid}/status').read_text().splitlines() if line.startswith('VmRSS:')))
        except (FileNotFoundError, ProcessLookupError, StopIteration):
            pass
        if time.monotonic()-saved >= 1:
            save()
            saved = time.monotonic()
        if time.monotonic()-started > 300 or peak > 6*1024*1024:
            limit = 'time' if time.monotonic()-started > 300 else 'memory'
            process.terminate()
            try:
                process.wait(timeout=2)
            except subprocess.TimeoutExpired:
                process.kill()
                process.wait()
            break
        time.sleep(0.025)
    code = process.wait()
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


def run_primary(rendered, out, build, *, inherited_debts, seconds=300):
    if not isinstance(inherited_debts, dict):
        raise ValueError('Inherited debts must be explicit')
    out, build = Path(out).resolve(), Path(build).resolve()
    out.mkdir(parents=True, exist_ok=True)
    if (out/'evidence.json').exists():
        raise ValueError('An existing native attempt must be reused, not repeated')
    path = out/'Boundary.v'
    source = instrument(rendered, seconds)
    path.write_text(source)
    wrapper = out/'compiler-wrapper'
    wrapper.write_text('#!/bin/sh\nexec ' + sys.executable + ' ' + str(Path(__file__).resolve()) + ' --compiler "$@"\n')
    wrapper.chmod(0o755)
    compiler_record = out/'compiler.json'
    tool = Path(__file__).resolve().parents[1]/'coqc_scratch.sh'
    command = [str(tool), str(path), str(build)]
    started = time.monotonic()
    done = subprocess.run(command, capture_output=True, text=True, env={**os.environ,
        'ZESU_SCRATCH_COQC_BINARY': str(wrapper), 'ZESU_PRIMARY_COMPILER_RECORD': str(compiler_record),
        'ZESU_PRIMARY_COMPILED_OBJECT': str(out/'Boundary.vo')})
    output = done.stdout + done.stderr
    log = out/'compiler.log'
    log.write_text(output)
    compiler = json.loads(compiler_record.read_text()) if compiler_record.exists() else None
    capture_error = None
    try:
        active = decode_active(output)
    except ValueError as error:
        active, capture_error = None, str(error)
    assumption = assumptions_result(output, rendered['lemma'])
    compiled = bool(done.returncode == 0 and compiler and compiler['exit_code'] == 0 and
                    compiler['limit'] is None and compiler['compiled_object'])
    outcome = ('native-qed-certificate' if compiled and assumption['verified'] else
               'automation-search-failure' if (compiler and compiler['limit']) or
                   'proof limit exceeded:' in output else
               'native-residual' if active or ('COQC-PRIMARY-BEGIN' in output and
                   'Attempt to save an incomplete proof' in output) else 'coqc-primary-unavailable')
    result = {'source': str(path), 'source_sha256': digest(path),
        'original_source_sha256': hashlib.sha256(rendered['source'].encode()).hexdigest(),
        'statement_sha256': rendered['statement_sha256'], 'entry_pc': rendered['entry_pc'],
        'entry_definition': rendered['entry_definition'], 'successors': rendered['successors'],
        'terminal_scope': rendered.get('terminal_scope'), 'scope': rendered['scope'],
        'setup_path': 'approved coqc primary fallback; no Pet start', 'scratch_command': command,
        'primary_tactic': 'try zesu_block.', 'primary_timeout': seconds,
        'budget_policy': 'The in-module tactic requests300seconds; the outer module limit includes imports and recording.',
        'primary_tactic_entered': 'COQC-PRIMARY-BEGIN' in output,
        'compiler': compiler, 'total_wall_seconds': time.monotonic()-started,
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
    raise SystemExit('Use run_primary with a validated native boundary')
