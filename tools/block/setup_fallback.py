#!/usr/bin/env python3
"""Measure frozen imports and entry elaboration without block execution."""
import argparse
import concurrent.futures
import hashlib
import json
import os
from pathlib import Path
import resource
import subprocess
import sys
import time


def digest(data):
    return hashlib.sha256(data).hexdigest()


def load_slice(source):
    marker = '\nProof.\n'
    if source.count(marker) != 1:
        raise ValueError('The frozen source must contain one lemma proof boundary')
    return source.split(marker)[0] + marker + 'Abort.\n'


def write_interactive_source(source):
    """Keep document loading separate from the explicit proof request."""
    source = Path(source)
    target = source.with_name(source.stem + '_interactive.v')
    contents = load_slice(source.read_text())
    if target.exists():
        if target.read_text() != contents:
            raise ValueError('The retained interactive source has different contents')
    else:
        target.write_text(contents)
    return target


def compiler_run(arguments):
    record = Path(os.environ['ZESU_FALLBACK_COMPILER_RECORD'])
    command = ['/home/cody/islaris/_opam/bin/coqc', *arguments]
    started = time.monotonic()
    process = subprocess.Popen(command)
    peak = 0
    limit = None
    while process.poll() is None:
        try:
            status = Path(f'/proc/{process.pid}/status').read_text()
            peak = max(peak, next(int(line.split()[1]) for line in status.splitlines()
                                  if line.startswith('VmRSS:')))
        except (FileNotFoundError, ProcessLookupError, StopIteration):
            pass
        if time.monotonic() - started > 60 or peak > 2 * 1024 * 1024:
            limit = 'time' if time.monotonic() - started > 60 else 'memory'
            process.terminate()
            try:
                process.wait(timeout=2)
            except subprocess.TimeoutExpired:
                process.kill()
                process.wait()
            break
        time.sleep(0.025)
    exit_code = process.wait()
    peak = max(peak, resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss)
    record.write_text(json.dumps({'compiler_pid': process.pid, 'command': command,
                                 'cwd': os.getcwd(), 'elapsed_seconds': time.monotonic() - started,
                                 'peak_rss_kib': peak, 'exit_code': exit_code, 'limit': limit,
                                 'limits': {'seconds': 60, 'rss_kib': 2 * 1024 * 1024}}, indent=2) + '\n')
    return exit_code if limit is None else 1


def run_one(source, out, build, wrapper, tool):
    original = source.read_bytes()
    sliced = load_slice(original.decode()).encode()
    target = out / source.name
    target.write_bytes(sliced)
    record = out / (source.stem + '.compiler.json')
    command = [str(tool), str(target.resolve()), str(build.resolve())]
    started = time.monotonic()
    result = subprocess.run(command, capture_output=True, text=True,
                            env={**os.environ, 'ZESU_SCRATCH_COQC_BINARY': str(wrapper.resolve()),
                                 'ZESU_FALLBACK_COMPILER_RECORD': str(record.resolve())})
    log = out / (source.stem + '.log')
    log.write_text(result.stdout + result.stderr)
    measured = json.loads(record.read_text()) if record.exists() else None
    if source.read_bytes() != original:
        raise ValueError('The frozen source changed during validation')
    return {'source': str(source.resolve()), 'source_sha256': digest(original),
            'slice': str(target.resolve()), 'slice_sha256': digest(sliced),
            'transformation': 'Exact prefix through Proof.; replace proof body with Abort.',
            'scratch_command': command, 'total_wall_seconds': time.monotonic() - started,
            'scratch_exit_code': result.returncode, 'compiler': measured,
            'log_sha256': digest(log.read_bytes()),
            'outcome': 'entry-elaborated' if result.returncode == 0 and measured and
                       measured['exit_code'] == 0 and measured['limit'] is None else 'fallback-failure'}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--sources', type=Path, required=True)
    parser.add_argument('--build', type=Path, required=True)
    parser.add_argument('--out', type=Path, required=True)
    args = parser.parse_args()
    out = args.out.resolve()
    out.mkdir(parents=True, exist_ok=True)
    tool = Path(__file__).resolve().parents[1] / 'coqc_scratch.sh'
    wrapper = out / 'compiler-wrapper'
    wrapper.write_text('#!/bin/sh\nexec ' + str(Path(sys.executable).resolve()) + ' ' +
                       str(Path(__file__).resolve()) + ' --compiler "$@"\n')
    wrapper.chmod(0o755)
    sources = sorted(path for path in args.sources.glob('*.v')
                     if any(path.name.startswith('block_' + pc + '_')
                            for pc in ('0x800d6974', '0x800d6a24', '0x800d6ac4')))
    if len(sources) != 6:
        raise ValueError('The fallback requires both frozen successors for each of three blocks')
    started = time.monotonic()
    rows = [run_one(sources[0], out, args.build, wrapper, tool)]
    if rows[0]['outcome'] == 'entry-elaborated':
        with concurrent.futures.ThreadPoolExecutor(max_workers=5) as pool:
            rows.extend(pool.map(lambda p: run_one(p, out, args.build, wrapper, tool), sources[1:]))
    report = {'label': 'Import and entry elaboration only; no block execution or closure',
              'inputs': {str(Path(__file__).resolve()): digest(Path(__file__).read_bytes()),
                         str(tool): digest(tool.read_bytes()),
                         str(args.build.resolve() / 'coqc_recipe.json'):
                         digest((args.build / 'coqc_recipe.json').read_bytes())},
              'workers': 5, 'representative_workers': 1,
              'elapsed_seconds': time.monotonic() - started, 'results': rows}
    (out / 'report.json').write_text(json.dumps(report, indent=2) + '\n')
    return 0 if len(rows) == 6 and all(r['outcome'] == 'entry-elaborated' for r in rows) else 1


if __name__ == '__main__':
    if sys.argv[1:2] == ['--compiler']:
        raise SystemExit(compiler_run(sys.argv[2:]))
    raise SystemExit(main())
