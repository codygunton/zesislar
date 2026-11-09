#!/usr/bin/env python3
"""Export the pure residual goals of one block as ready-to-use goal dirs (diagnostic only).

Usage:
  export_block.py --block <case> --bank <bank dir with ARGS.json> --out <new dir> [--heavy]
                  [--mode failed-calls|final-open] [--caller-import MODULE]
  export_block.py --compare <MANIFEST.json> <MANIFEST.json>

Steps, all in one resource-guard batch (one scope per compile):
 1. Probe the live Ltac bodies of the block's plain caller (CALLERS24.json) and keep
    the faithful copies.
 2. Run the caller in census residual mode: the SearchBudget size guard plus a
    diagnostic per-call limit (--call-seconds, default 300) inside the guard scope.
 3. Collect every pure goal where the selected-facts solver fails, and package each
    as <out>/<block>-<n>/ (goal.v, goal_full.v, FACTS.md, check.sh, CONTROL).
    The whole-context control marks a goal `true` (passed) or `unknown` (did not
    pass); unknown goals stay. Non-pure goals go to <out>/spatial.tsv.
 4. Write <out>/MANIFEST.json: block, bank, main sha, goals, controls, run times.

--mode final-open runs the plain `zesu_block2` and exports only the goals it leaves
open (no failed-call dumps, no solver retry); spatial goals go to spatial.tsv and
spatial/<n>.txt with their Lithium judgment. --caller-import adds one import after the
caller's last import (for example a diagnostic solver configuration).

The goal list depends only on the bank and the block. `--compare` checks two
manifests for equality without their run times. Timeouts are allowed here because
this is a diagnostic tool; they never belong in production tactics."""
from concurrent.futures import ThreadPoolExecutor
from datetime import datetime, timezone
from pathlib import Path
import argparse
import hashlib
import json
import os
import shutil
import subprocess
import sys
import time

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import census_gen  # noqa: E402
import guarded  # noqa: E402
import ltac_probe  # noqa: E402
import residual_package as pkg  # noqa: E402

ROOT = HERE.parents[1]
CALLERS = '/home/cody/zesislar/_build/agents/spec-a/composition403/integration645/CALLERS24.json'
COQ_BIN = '/home/cody/islaris/_opam/bin'
BASE_ENV = dict(ZESU_MODULE_CLAIM_BYTES='2147483648', ZESU_MODULE_LIMIT_GIB='16', ZESU_GATE_MODULE_LIMIT_GIB='16',
                ZESU_BATCH_LIMIT='200G', ZESU_PROOF_CPU_LIMIT='unlimited', ZESU_SCOPE_CPU='unlimited')
# Heavy blocks (6a78, 698c, ...): the issue-10 diagnostic probe class with a 64 GiB scope.
HEAVY_ENV = dict(ZESU_DIAGNOSTIC_PROBE='1', ZESU_PROBE_ISSUE='10', ZESU_MODULE_LIMIT_GIB='64',
                 ZESU_GATE_MODULE_LIMIT_GIB='64', ZESU_BATCH_LIMIT='200G', ZESU_PROOF_CPU_LIMIT='unlimited')
CENSUS_FLAGS = ['--print-all', '--fact-limit', '100000', '--dump-fail', 'Lia.lia,tactics.bv_solve',
                '--fail-props', '-1']
COORD_VARS = ('COORD_AGENT', 'COORD_ROOT')


def utc():
    return datetime.now(timezone.utc).strftime('%Y-%m-%dT%H:%M:%SZ')


def sha256(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def git_head():
    r = subprocess.run(['git', '-C', str(ROOT), 'rev-parse', 'HEAD'], capture_output=True, text=True)
    return r.stdout.strip() or None


def caller_of(block, callers):
    rows = [r for r in json.loads(Path(callers).read_text()) if r['case'] == block]
    if not rows:
        raise SystemExit('no caller for block %s in %s' % (block, callers))
    return rows[0]


def bank_info(bank):
    bank = Path(bank).resolve()
    args_json = bank / 'ARGS.json'
    if not args_json.exists():
        raise SystemExit('%s has no ARGS.json' % bank)
    meta = json.loads((bank / 'BANK.json').read_text()) if (bank / 'BANK.json').exists() else {}
    args = guarded.coqc_args(args_json)
    lib = Path([args[i + 1] for i, x in enumerate(args) if x == '-Q' and args[i + 2] == 'ZesuSsz'][0]).parent
    return dict(path=str(bank), args_json=str(args_json), args_sha256=sha256(args_json),
                main=meta.get('main'), lib=lib, args=args)


PLUGINS = (('plugin', 'ZesuSsz/Evidence/GatesPlugin', 'signature_gates_plugin'),
           ('trace-observer', 'tools/block/TracePlugin', 'trace_block_plugin'))


def findlib_dir(bank, out):
    """A findlib directory that holds the bank's `zesu-signature-gates` plugins.
    A bank holds only build artifacts, so this links them in the install layout."""
    lib = Path(bank['lib'])
    installed = lib.parent / 'install/default/lib'
    if (installed / 'zesu-signature-gates/META').exists():
        return installed
    root = out / '_findlib'
    pkg_dir = root / 'zesu-signature-gates'
    pkg_dir.mkdir(parents=True)
    shutil.copyfile(lib / 'META.zesu-signature-gates', pkg_dir / 'META')
    for sub, src, stem in PLUGINS:
        (pkg_dir / sub).mkdir()
        for f in sorted((lib / src).glob(stem + '.*')) + sorted((lib / src / ('.%s.objs' % stem) / 'byte').glob(stem + '.cm[it]')):
            (pkg_dir / sub / f.name).symlink_to(f)
    return root


def in_batch(a, argv):
    """Re-run this command inside one guard batch unless it already runs in one."""
    if os.environ.get('ZESU_IN_BATCH'):
        return None
    env = {k: v for k, v in os.environ.items() if k not in COORD_VARS}
    env.update(BASE_ENV)
    if a.heavy:
        env.update(HEAVY_ENV)
    env['PATH'] = COQ_BIN + ':' + env.get('PATH', '/usr/bin:/bin')
    out_key = hashlib.sha256(str(Path(a.out).resolve()).encode()).hexdigest()[:6]
    cmd = [guarded.guard_path(), 'batch', 'residual-export-%s-%s' % (a.block, out_key), '--',
           sys.executable, '-u', str(Path(__file__).resolve())] + argv
    return subprocess.run(cmd, env=env).returncode


def build(c, block, prefix, stage, args, workers_tag, control_seconds):
    d = stage / c['id']
    name = pkg.stage_files(c, block, prefix, d)
    tag = '%s-%s' % (workers_tag, c['id'])
    # control.v holds the goal_full.v statement, so a passing control also shows that it reparses.
    control = guarded.compile_file(d / 'control.v', tag + 'c', args, limit_s=control_seconds)
    goal = guarded.compile_file(d / 'goal.v', tag + 'g', args, limit_s=600)
    render = guarded.compile_file(d / 'render.v', tag + 'r', args, limit_s=600)
    return dict(name=name, control=control, goal=goal, render=render)


def census_mode(a):
    return 'residual' if a.mode == 'failed-calls' else 'final-open'


def flags_of(a):
    if a.mode == 'failed-calls':
        return CENSUS_FLAGS
    return [f for i, f in enumerate(CENSUS_FLAGS)
            if f != '--dump-fail' and (i == 0 or CENSUS_FLAGS[i - 1] != '--dump-fail')]


def with_import(src, module):
    lines = src.split('\n')
    last = max(i for i, l in enumerate(lines) if l.startswith(('Require ', 'From ')))
    lines.insert(last + 1, 'Require Import %s.' % module)
    return '\n'.join(lines)


def stalled_calls(text):
    """Solver layers that hit the diagnostic limit, in log order."""
    return [line.split(' E ', 1)[1].split()[0] for line in text.splitlines()
            if ' E ' in line and line.rstrip().endswith(' timeout') and 'CENSUS' in line]


def export(a):
    t_start = time.monotonic()
    started = utc()
    out = Path(a.out).resolve()
    if out.exists() and any(out.iterdir()):
        raise SystemExit('%s exists and is not empty; give a new --out' % out)
    out.mkdir(parents=True, exist_ok=True)
    work = out / '_work'
    work.mkdir()
    bank = bank_info(a.bank)
    args = bank['args']
    ocamlpath = str(findlib_dir(bank, out))
    os.environ['OCAMLPATH'] = ocamlpath
    row = caller_of(a.block, a.callers)
    caller_src_path = Path(row['caller'])
    if sha256(caller_src_path) != row.get('caller_sha256', sha256(caller_src_path)):
        raise SystemExit('caller %s does not match its CALLERS24 sha256' % caller_src_path)
    caller = work / ('Caller%s.v' % a.block)
    shutil.copyfile(caller_src_path, caller)
    if a.caller_import:
        caller.write_text(with_import(caller.read_text(), a.caller_import))
    tag = 'residual-export-%s-%s' % (a.block, hashlib.sha256(str(out).encode()).hexdigest()[:6])
    times = {}

    t = time.monotonic()
    probe_dir = work / 'probe'
    probe = ltac_probe.probe(caller, probe_dir, args, tag + '-probe')
    times['probe'] = round(time.monotonic() - t, 1)
    t = time.monotonic()
    verify, excluded = ltac_probe.verify(caller, probe_dir, work / 'verify', args, tag)
    times['verify'] = round(time.monotonic() - t, 1)

    t = time.monotonic()
    census_v = work / ('Census%s.v' % a.block)
    census_gen.main([str(caller), str(census_v), '--mode', census_mode(a), '--timeout', str(a.call_seconds)] +
                    flags_of(a) + ['--ltacs', str(probe_dir / 'ltacs.json'),
                                    '--fullnames', str(probe_dir / 'fullnames.json'),
                                    '--exclude', ','.join(excluded)])
    census = guarded.compile_file(census_v, tag + '-census', args, stamp=True, attempts=1)
    times['census'] = round(time.monotonic() - t, 1)
    log = census_v.with_suffix('.log')
    text = log.read_text(errors='replace')
    if census['status'] != 'pass' or 'CENSUS STAGE dump-done' not in text:
        raise SystemExit('census run did not finish (%s, rc %d); see %s' % (
            census['status'], census['returncode'], log))

    t = time.monotonic()
    caller_src = caller.read_text()
    evars = pkg.entry_vars(caller_src, bank['lib'])
    tries, spatial, uniq = pkg.candidates(log, a.block, a.fact_limit, evars,
                                          fail_dumps=a.mode == 'failed-calls')
    stalls = stalled_calls(text)
    pkg.write_spatial(out, spatial)
    stage = work / 'stage'
    prefix = pkg.prefix_of(caller_src)
    with ThreadPoolExecutor(max_workers=a.workers) as pool:
        results = list(pool.map(lambda c: build(c, a.block, prefix, stage, args, tag, a.control_seconds), uniq))
    path_env = COQ_BIN + ':/usr/local/bin:/usr/bin:/bin'
    goals = []
    control_dir = work / 'control'
    for c, res in zip(uniq, results):
        pkg.write_goal_dir(out, c, a.block, stage / c['id'], res, args, guarded.guard_path(), path_env, a.fact_limit,
                           ocamlpath)
        (control_dir / c['id']).mkdir(parents=True)
        shutil.copyfile(stage / c['id'] / 'control.v', control_dir / c['id'] / 'control.v')
        goals.append(pkg.goal_record(c, res))
    times['package'] = round(time.monotonic() - t, 1)
    times['total'] = round(time.monotonic() - t_start, 1)
    times['census_compile'] = census['seconds']

    manifest = dict(
        block=a.block,
        bank=dict(path=bank['path'], main=bank['main'], args_sha256=bank['args_sha256']),
        out=str(out), ocamlpath=ocamlpath,
        main_sha=bank['main'], tool_commit=git_head(),
        caller=dict(path=str(caller_src_path), sha256=sha256(caller_src_path)),
        mode=a.mode, caller_import=a.caller_import, stalls=stalls,
        spatial_goals=[dict(n=r['n'], kind=r['kind'], judgment=r['judgment']) for r in spatial],
        settings=dict(call_seconds=a.call_seconds, control_seconds=a.control_seconds, fact_limit=a.fact_limit,
                      census_flags=flags_of(a), heavy=a.heavy),
        probe=dict(probe, **verify), excluded=sorted(excluded),
        tries=tries, spatial=len(spatial), unique=len(uniq),
        goal_list=[g['id'] + ':' + g['sha'] for g in goals],
        controls={g['id']: g['control'] for g in goals},
        counts=dict(goals=len(goals), true=sum(1 for g in goals if g['truth'] == 'true'),
                    unknown=sum(1 for g in goals if g['truth'] == 'unknown'), spatial=len(spatial),
                    goal_reparse_fail=sum(1 for g in goals if not g['goal_reparses'])),
        goals=goals, run_times=times, started_utc=started, finished_utc=utc())
    (out / 'MANIFEST.json').write_text(json.dumps(manifest, indent=1) + '\n')
    print(json.dumps(dict(block=a.block, out=str(out), **manifest['counts'], run_times=times)))
    return 0


def main(argv=None):
    argv = sys.argv[1:] if argv is None else argv
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument('--block')
    ap.add_argument('--bank')
    ap.add_argument('--out')
    ap.add_argument('--callers', default=CALLERS)
    ap.add_argument('--call-seconds', type=int, default=300, help='diagnostic per-call solver limit')
    ap.add_argument('--control-seconds', type=int, default=300)
    ap.add_argument('--fact-limit', type=int, default=1500, help='selection: drop facts above this many nodes')
    ap.add_argument('--workers', type=int, default=8, help='packaging compiles at once (at most 16)')
    ap.add_argument('--heavy', action='store_true', help='issue-10 probe class with a 64 GiB scope')
    ap.add_argument('--compare', nargs=2, metavar='MANIFEST')
    ap.add_argument('--mode', default='failed-calls', choices=['failed-calls', 'final-open'],
                    help='failed-calls: every failed solver call; final-open: goals zesu_block2 leaves open')
    ap.add_argument('--caller-import', help='module imported after the caller\'s last import')
    a = ap.parse_args(argv)
    if a.compare:
        m1, m2 = (json.loads(Path(p).read_text()) for p in a.compare)
        diffs = pkg.compare(m1, m2)
        print(json.dumps(dict(equal=not diffs, differences=diffs)))
        return 0 if not diffs else 1
    if not (a.block and a.bank and a.out):
        ap.error('--block, --bank and --out are required')
    if not 1 <= a.workers <= 16:
        ap.error('--workers must be between 1 and 16')
    rc = in_batch(a, argv)
    if rc is not None:
        return rc
    return export(a)


if __name__ == '__main__':
    sys.exit(main())
