#!/usr/bin/env python3
"""Shared sweep and sample runner: compile unmodified generated callers at Qed on one bank, certify each.

usage: sweep.py --build DIR --callers NAME --run-dir DIR [--jobs N] [--limit-gib N] [--limits LIMITS.json]
                [--cpu SECONDS] CASE...

Each case gets a fresh directory RUN_DIR/runs/<case>[-n] holding a byte copy of
tools/block/generated/NAME/Caller<case>.v at the bank's head (the HEAD of the bank's workspace).
closure_cert.compile_caller compiles it with the bank's coqc recipe under the resource guard (batch and
scope) through tools/measure.py; closure_cert.verdict then writes CLOSURE.json or NOT-CLOSED.json
beside it. Each case prints one line

    RUN-DONE case=C coqc_rc=N verdict=CLOSED|NOT-CLOSED [reason="..."]

coqc_rc is coqc's own exit status from measure.json ("none": coqc reported none), never the exit of
the guard or of this script: the guard returns 0 for a failed compile. Only verdict=CLOSED is a
closure. RUN_DIR/sweep.jsonl gets one row per case; `closed` is true only with a certificate. Recount
rows with tools/sweep_outcome.py. LIMITS.json maps a case to its memory limit in GiB (last peak x 1.25).

Launch: tools/bg --heavy NAME python3 tools/sweep.py ...
"""
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path
import argparse
import json
import sys
import threading
import time

sys.path.insert(0, str(Path(__file__).resolve().parent))
import closure_cert as C
import sweep_outcome as S

ROWS_LOCK = threading.Lock()


def fresh_directory(run_dir, case):
    directory, number = run_dir / 'runs' / case, 2
    while directory.exists():
        directory, number = run_dir / 'runs' / ('%s-%d' % (case, number)), number + 1
    directory.mkdir(parents=True)  # a fresh directory: cold solver caches
    return directory


def row_for(case, record, wrapper_exit, seconds, log_text):
    measured = record.get('cpu_seconds') is not None
    row = dict(case=case, verdict=record['verdict'], closed=record['verdict'] == 'CLOSED',
               returncode=record.get('coqc_returncode'), wrapper_exit=wrapper_exit,
               reason=record.get('reason'), seconds=seconds, cpu_seconds=record.get('cpu_seconds'),
               max_rss_gib=record.get('peak_gib'), stall=None, certificate=record.get('file'))
    row['status'] = S.outcome(row['returncode'], measured, log_text=log_text, certified=row['closed'])
    return row


def run(case, options, workspace, head, limits):
    directory = fresh_directory(options.run_dir, case)
    generated = '%s/%s/Caller%s.v' % (C.GENERATED, options.callers, case)
    caller = directory / Path(generated).name
    caller.write_bytes(C.git(workspace, 'cat-file', 'blob', head + ':' + generated).stdout)
    start = time.monotonic()
    wrapper_exit = C.compile_caller(case, caller, options.build, directory, limits.get(case, options.limit_gib),
                                    options.cpu, name='sweep-%s-%s' % (options.run_dir.name, case))
    record = C.verdict(case, caller, options.build, directory / 'measure.json', head=head, out=directory)
    log_text = (directory / 'run.log').read_text(errors='replace')
    row = row_for(case, record, wrapper_exit, round(time.monotonic() - start), log_text)
    with ROWS_LOCK:
        with (options.run_dir / 'sweep.jsonl').open('a') as rows:
            rows.write(json.dumps(row) + '\n')
        print(C.done_line(record), flush=True)
    return row


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument('cases', nargs='+')
    parser.add_argument('--build', type=Path, required=True)
    parser.add_argument('--callers', required=True, help='generated callers directory name, e.g. '
                        'decodeparentheader_fp301_callers')
    parser.add_argument('--run-dir', type=Path, required=True)
    parser.add_argument('--jobs', type=int, default=1)
    parser.add_argument('--limit-gib', type=int, default=16)
    parser.add_argument('--limits', type=Path)
    parser.add_argument('--cpu', type=int)
    options = parser.parse_args(argv)
    options.run_dir = options.run_dir.resolve()
    options.run_dir.mkdir(parents=True, exist_ok=True)
    limits = json.loads(options.limits.read_text()) if options.limits else {}
    workspace = C.bank_workspace(options.build)
    head = C.resolve_head(workspace, None)
    item = options.run_dir / 'ITEM.json'
    if not item.exists():
        branch = C.git(workspace, 'branch', '--show-current').stdout.decode().strip()
        item.write_text(json.dumps({'branch': branch, 'head': head}) + '\n')
    with ThreadPoolExecutor(max_workers=options.jobs) as pool:
        rows = list(pool.map(lambda case: run(case, options, workspace, head, limits), options.cases))
    print('SUMMARY certified closed', sum(row['closed'] for row in rows), 'of', len(rows), 'at', head[:12],
          flush=True)
    return 0


if __name__ == '__main__':
    sys.exit(main())
