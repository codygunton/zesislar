#!/usr/bin/env python3
"""BENCH: run a fixed block set at Qed with telemetry, then rank where CPU, memory and failures go.

usage:
  bench.py run --set NAME --head REV [--rules-commit REV] --run-dir DIR [--jobs N] [--no-telemetry]
               [--callers] [--only CASE ...]
  bench.py report RUN_DIR [--base RUN_DIR] [--json]

run (launch it with `tools/bg --heavy bench-<tag> python3 tools/bench/bench.py run ...`):
 1. Workspace: a git worktree .worktrees/bench-<key> on branch bench/<key>, at REV with the set's
    overlay commits merged (sets/NAME.json "overlays"; functions that are not on main) and, with
    --rules-commit, the rule trees (ZesuSsz/Automation2, ZesuSsz/Automation, InstrSpecs,
    ZesuSsz/Proofs/Tests) taken from that commit. <key> hashes REV, the rules commit and the overlays,
    so a second run on the same inputs reuses the worktree and its bank. When the run ends (also on
    failure) bench.py removes the worktree and its bank (`build_janitor.py remove-worktree`, which
    saves goals and closure records first) unless --keep-bank asks to keep them for that reuse.
 2. Bank: _build/agents/bench-<key> in that worktree: `make stock-native-indexes` and one Dune build
    of @install plus the modules the set's callers import (never the other callers). BANK.json
    records the targets; a later run with no new target skips the build. Blocks compile with the
    bank's coqc recipe (coqc_recipe.json). A bank built wholly from the Dune cache runs no coqc, so
    its trace holds no recipe: then `dune rules` of one bank target gives the same command. With
    no recipe either way the run stops with one `refused:` line (exit 3) before any block.
 3. Blocks: every member, longest expected first, JOBS at a time (default: the set's "jobs"). Each
    compiles the unmodified generated caller at the bench head through tools/closure_cert.py
    (resource guard batch + scope, CPU cap and memory limit from the set's "caps", where a member's
    own "cpu_seconds" replaces the CPU cap, claim from the member's claim_gib) with ZESU_TELEMETRY=1
    (with --callers also ZESU_TELEMETRY_CALLERS=1: each
    Ltac1 solver record names its Ltac caller; a diagnostic, it slows the run), and gets
    CLOSURE.json or NOT-CLOSED.json. A sampler
    thread finds the compile's coqc and writes samples.jsonl every second (time, RSS, peak RSS, CPU,
    bytes of coqc output so far) and runs `perf stat -e instructions:u -p <coqc>` into perf.csv.
    Leftover goals the telemetry prints are saved with tools/save_goal.py
    (tag bench-<run dir name>). The telemetry prints only pure goals (a spatial one is
    `@@X skip final spatial`); with --dump-leftover an open block that has such a skip is compiled
    once more from a scratch copy whose closing `Qed.` is `Show. Abort.` (same caps), and the
    printed goals go to <block>/leftover/FINAL-GOAL.txt (row field leftover_dump). One row per
    block goes to RUN_DIR/results.jsonl.

report: one table per block (verdict, how it ended, CPU, instructions, peak, stage reached, stage
times and steps, top 5 solver calls by time and by RSS growth, leftover goal classes), then a
ranking of stages, solver kinds and sites by CPU and memory over the set. --base adds per-block
and set deltas. Writes REPORT.md and REPORT.json into RUN_DIR and prints the markdown.
"""
from concurrent.futures import ThreadPoolExecutor
from datetime import datetime, timezone
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import threading
import time

BENCH = Path(__file__).resolve().parent
TOOLS = BENCH.parent
sys.path.insert(0, str(TOOLS))
sys.path.insert(0, str(BENCH))
import bench_report as R  # noqa: E402
import build_janitor as J  # noqa: E402
import closure_cert as C  # noqa: E402
from coqc_findlib import RECORD_NAME as OCAMLPATH_RECORD, check_record  # noqa: E402
from coqc_recipe import project_recipe, remember_recipe  # noqa: E402
from dune_build_dir import physical_working_dir  # noqa: E402

RULE_TREES = ('ZesuSsz/Automation2', 'ZesuSsz/Automation', 'InstrSpecs', 'ZesuSsz/Proofs/Tests')
ISLARIS = Path(os.environ.get('ISLARIS_REPO', str(Path.home() / 'islaris')))
IMPORT = re.compile(r'^\s*(?:From\s+(\S+)\s+)?Require\s+(?:Import\s+|Export\s+)?(.+?)\.\s*$', re.M)
ROWS_LOCK = threading.Lock()


def now():
    return datetime.now(timezone.utc).isoformat()


def git(directory, *args, check=True):
    result = subprocess.run(['git', '-C', str(directory), *args], capture_output=True, text=True)
    if check and result.returncode:
        raise SystemExit('git %s failed: %s' % (' '.join(args), result.stderr.strip()))
    return result.stdout.strip()


def repo_root():
    common = Path(git(TOOLS, 'rev-parse', '--path-format=absolute', '--git-common-dir'))
    return common.parent


def load_set(name):
    path = Path(name) if name.endswith('.json') else BENCH / 'sets' / (name + '.json')
    data = json.loads(path.read_text())
    for member in data['members']:
        for field in ('function', 'callers', 'case'):
            if field not in member:
                raise SystemExit('%s: member %s lacks %s' % (path, member, field))
    return data


# ---------------------------------------------------------------- workspace

def workspace_key(head, rules, overlays):
    text = '\n'.join([head, rules or '-'] + [overlay['commit'] for overlay in overlays])
    return hashlib.sha256(text.encode()).hexdigest()[:10]


def commit_message(subject, lines):
    return subject + '\n\n' + '\n'.join(lines) + '\n\nCo-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>\n'


def prepare_workspace(root, head, rules, overlays):
    """The measured worktree and its HEAD (head + overlays + rule trees of rules)."""
    key = workspace_key(head, rules, overlays)
    path = root / '.worktrees' / ('bench-' + key)
    marker = 'bench-key: ' + key
    if path.is_dir():
        if git(path, 'status', '--porcelain', '--untracked-files=no'):
            raise SystemExit('%s has uncommitted changes; it is not a clean measured head' % path)
        if marker not in git(path, 'log', '-1', '--format=%B'):
            raise SystemExit('%s exists but its HEAD is not a finished bench head (%s)' % (path, marker))
        return key, path, git(path, 'rev-parse', 'HEAD')
    git(root, 'worktree', 'add', '-q', '-b', 'bench/' + key, str(path), head)
    for overlay in overlays:
        if subprocess.run(['git', '-C', str(path), 'merge-base', '--is-ancestor', overlay['commit'], 'HEAD']).returncode:
            git(path, 'merge', '-q', '--no-ff', '--no-edit', '-m', commit_message(
                'BENCH: merge overlay %s (%s)' % (overlay['name'], overlay['commit'][:12]),
                ['Measurement head only; never merged to main.']), overlay['commit'])
    if rules:
        git(path, 'rm', '-rq', '--ignore-unmatch', '--', *RULE_TREES)
        git(path, 'checkout', rules, '--', *RULE_TREES)
    git(path, 'commit', '-q', '--allow-empty', '-m', commit_message(
        'BENCH head: %s%s' % (head[:12], ', rules %s' % rules[:12] if rules else ''),
        ['head %s' % head, 'rules %s' % (rules or head)] + ['overlay %s %s' % (o['name'], o['commit']) for o in overlays]
        + [marker]))
    for tree in RULE_TREES if rules else ():
        if git(path, 'rev-parse', 'HEAD:' + tree, check=False) != git(path, 'rev-parse', rules + ':' + tree, check=False):
            raise SystemExit('rule tree %s differs from %s in %s' % (tree, rules[:12], path))
    return key, path, git(path, 'rev-parse', 'HEAD')


# ---------------------------------------------------------------- bank

def caller_path(member):
    return '%s/%s/Caller%s.v' % (C.GENERATED, member['callers'], member['case'])


def bank_targets(workspace, bench_head, members):
    """.vo targets for every project module the members' callers import."""
    targets = set()
    for member in members:
        text = git(workspace, 'cat-file', 'blob', '%s:%s' % (bench_head, caller_path(member)))
        for match in IMPORT.finditer(text):
            prefix = match.group(1)
            for module in match.group(2).split():
                name = '%s.%s' % (prefix, module) if prefix else module
                if not name.startswith('ZesuSsz.'):
                    continue
                source = Path(*name.split('.')).with_suffix('.v')
                if (workspace / source).is_file():
                    targets.add(source.with_suffix('.vo').as_posix())
    return sorted(targets)


def bank_environment(workspace):
    environment = {key: value for key, value in os.environ.items()
                   if key not in ('COORD_AGENT', 'COORD_ROOT', 'OCAMLPATH')}
    environment['PATH'] = os.pathsep.join([str(workspace / 'bin'), str(ISLARIS / 'bin'), environment.get('PATH', '')])
    environment.setdefault('TMPDIR', str(Path.home() / '.cache/orch-checkfast-tmp'))
    return environment


def refuse(message):
    print('refused: ' + message, file=sys.stderr, flush=True)
    raise SystemExit(3)


def rule_command(action, directory=None):
    """(working dir, [program, *args]) of the first `run` in a `dune rules --format=json` action."""
    if not isinstance(action, list) or not action:
        return None
    if action[0] == 'chdir' and len(action) == 3:
        return rule_command(action[2], action[1])
    if action[0] == 'run':
        return directory, action[1:]
    for child in action[1:]:
        found = rule_command(child, directory)
        if found:
            return found
    return None


def rules_recipe(rules):
    """The coqc recipe (coqc_recipe.json shape) of a project module in parsed `dune rules` JSON."""
    for rule in rules:
        found = rule_command(rule.get('action'))
        if found and Path(found[1][0]).name == 'coqc':
            recipe = {'command': found[1], 'working_dir': found[0]}
            if project_recipe(recipe):
                return recipe
    return None


def ensure_recipe(workspace, key, bank, targets, log):
    """Give the bank a coqc recipe before any block runs. A bank built wholly from the Dune cache
    runs no coqc, so its trace has none; `dune rules` of one target prints the command Dune would run."""
    if project_recipe(remember_recipe(bank)):
        return
    target = next((target for target in targets if target.startswith('ZesuSsz/')), None)
    fix = 'rebuild one bank target without the cache (`dune build --cache=disabled`) or copy coqc_recipe.json ' \
          'from a bank of the same head'
    if target is None:
        refuse('bank %s has no coqc recipe and no project target to ask `dune rules`; %s' % (bank, fix))
    output = bank / 'recipe-rules.json'
    output.unlink(missing_ok=True)
    with (workspace / ('bench-%s-bank.log' % key)).open('a') as out:
        rc = subprocess.run([sys.executable, str(workspace / 'tools/dune_trace_guard.py'), '--canonical-build-dir', '--',
                             'opam', 'exec', '--switch=' + str(ISLARIS), '--', 'dune', 'rules', '--format=json',
                             '--root', '.', '--build-dir', str(bank), '--trace-file', str(bank / 'recipe-rules.trace.csexp'),
                             '-o', str(output), target],
                            cwd=workspace, env=bank_environment(workspace), stdout=out,
                            stderr=subprocess.STDOUT).returncode
    recipe = rules_recipe(json.loads(output.read_text())) if rc == 0 and output.is_file() else None
    if recipe is None:
        refuse('bank %s has no coqc recipe (a cache-only build runs no coqc) and `dune rules %s` gave none '
               '(rc %d); %s' % (bank, target, rc, fix))
    recipe['working_dir'] = physical_working_dir(bank, recipe['working_dir'])
    pending = bank / '.coqc_recipe.json.pending'
    pending.write_text(json.dumps(recipe) + '\n')
    pending.replace(bank / 'coqc_recipe.json')
    log('bank %s: coqc recipe from `dune rules %s` (the build ran no coqc)' % (bank, target))


def ensure_ocamlpath(workspace, bank, log):
    """Give the bank its compiler findlib record (coqc-ocamlpath.json, read by closure_cert.py and
    render_function.sh). Dune's coqc route (tools/dune_coqc_route.sh -> coqc_findlib.py record)
    writes it when the build runs a coqc; a build wholly from the Dune cache runs none. Dune gives
    its actions OCAMLPATH = <build>/install/default/lib in front of the ambient value, and
    bank_environment removes the ambient one, so the record is exactly that path."""
    record = bank / OCAMLPATH_RECORD
    if record.is_file():
        return
    library = bank.resolve() / 'install' / 'default' / 'lib'
    if not library.is_dir():
        refuse('bank %s has no %s and no %s to record (the @install build left no findlib directory)'
               % (bank, OCAMLPATH_RECORD, library))
    data = {'schema_version': 1, 'workspace': str(Path(workspace).resolve()), 'private_build': str(bank.resolve()),
            'OCAMLPATH': str(library)}
    check_record(data, workspace, bank)
    pending = bank / ('.%s.pending' % OCAMLPATH_RECORD)
    pending.write_text(json.dumps(data, sort_keys=True) + '\n')
    pending.replace(record)
    log('bank %s: %s written (the build ran no coqc)' % (bank, OCAMLPATH_RECORD))


def build_bank(workspace, key, bench_head, targets, make_vars, log):
    bank = workspace / '_build' / 'agents' / ('bench-' + key)
    record = bank / 'BANK.json'
    if record.is_file():
        old = json.loads(record.read_text())
        if old.get('rc') == 0 and old.get('head') == bench_head and set(targets) <= set(old.get('targets', [])):
            log('bank %s reused (%d targets)' % (bank, len(targets)))
            ensure_recipe(workspace, key, bank, targets, log)
            ensure_ocamlpath(workspace, bank, log)
            return bank
    environment = bank_environment(workspace)
    Path(environment['TMPDIR']).mkdir(parents=True, exist_ok=True)
    started = now()
    with (workspace / ('bench-%s-bank.log' % key)).open('a') as out:
        prep = subprocess.run(['make', '--no-print-directory', 'stock-native-indexes', 'AGENT_BUILD_DIR=' + str(bank)]
                              + ['%s=%s' % item for item in sorted(make_vars.items())],
                              cwd=workspace, env=environment, stdout=out, stderr=subprocess.STDOUT).returncode
        rc = prep
        if prep == 0:
            rc = subprocess.run([str(workspace / 'tools/resource_guard.sh'), 'batch', 'bench-%s-bank' % key, '--',
                                 sys.executable, str(workspace / 'tools/dune_trace_guard.py'), '--canonical-build-dir', '--',
                                 'opam', 'exec', '--switch=' + str(ISLARIS), '--', 'dune', 'build', '--root', '.',
                                 '--build-dir', str(bank), '--cache=enabled', '-j8', '@install', *targets],
                                cwd=workspace, env=environment, stdout=out, stderr=subprocess.STDOUT).returncode
    missing = [target for target in targets if not (bank / 'default' / target).is_file()]
    bank.mkdir(parents=True, exist_ok=True)
    record.write_text(json.dumps({'head': bench_head, 'targets': targets, 'prep_rc': prep,
                                  'rc': rc if not missing else (rc or 1), 'missing': missing,
                                  'started_utc': started, 'ended_utc': now()}, indent=1) + '\n')
    if rc or missing:
        raise SystemExit('bank build failed (prep rc %d, build rc %d, %d targets missing); see %s'
                         % (prep, rc, len(missing), workspace / ('bench-%s-bank.log' % key)))
    log('bank %s built (%d targets)' % (bank, len(targets)))
    ensure_recipe(workspace, key, bank, targets, log)
    ensure_ocamlpath(workspace, bank, log)
    return bank


# ---------------------------------------------------------------- sampler

def find_coqc(caller):
    """PID of the coqc compiling this caller (its path is unique to the run directory)."""
    needle = str(caller).encode()
    for entry in os.scandir('/proc'):
        if not entry.name.isdigit():
            continue
        try:
            with open('/proc/%s/cmdline' % entry.name, 'rb') as handle:
                argv = handle.read().split(b'\0')
        except OSError:
            continue
        if argv and Path(argv[0].decode(errors='replace')).name == 'coqc' and needle in argv:
            return int(entry.name)
    return None


def proc_sample(pid):
    """(rss_kib, hwm_kib, cpu_s) of a live process, or None once it is gone."""
    try:
        status = Path('/proc/%d/status' % pid).read_text()
        stat = Path('/proc/%d/stat' % pid).read_text()
    except OSError:
        return None
    fields = {line.split(':')[0]: line.split()[1] for line in status.splitlines() if line.startswith(('VmRSS', 'VmHWM'))}
    if 'VmRSS' not in fields:
        return None  # a zombie: exited, not yet reaped
    ticks = stat[stat.rindex(')') + 2:].split()
    cpu = (int(ticks[11]) + int(ticks[12])) / os.sysconf('SC_CLK_TCK')
    return int(fields['VmRSS']), int(fields.get('VmHWM', 0)), round(cpu, 2)


class Sampler(threading.Thread):
    """Every second: the compile's coqc RSS, peak RSS, CPU and log size, into samples.jsonl."""

    def __init__(self, directory, caller):
        super().__init__(daemon=True)
        self.directory, self.caller = Path(directory), Path(caller).resolve()
        self.done = threading.Event()
        self.pid = self.perf = None

    def run(self):
        log = self.directory / 'measure.json.log'
        with (self.directory / 'samples.jsonl').open('a') as out:
            while not self.done.is_set():
                if self.pid is None:
                    self.pid = find_coqc(self.caller)
                    if self.pid is not None:
                        (self.directory / 'coqc.pid').write_text('%d\n' % self.pid)
                        self.perf = subprocess.Popen(['perf', 'stat', '-x,', '-e', 'instructions:u', '-p', str(self.pid),
                                                      '-o', str(self.directory / 'perf.csv')],
                                                     stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
                if self.pid is not None:
                    sample = proc_sample(self.pid)
                    if sample is None:
                        break
                    size = log.stat().st_size if log.exists() else 0
                    out.write(json.dumps({'t': round(time.time(), 2), 'rss_kib': sample[0], 'hwm_kib': sample[1],
                                          'cpu_s': sample[2], 'log_bytes': size}) + '\n')
                    out.flush()
                self.done.wait(1.0)
        if self.perf is not None:
            try:
                self.perf.wait(timeout=30)  # perf stat -p ends when its target exits
            except subprocess.TimeoutExpired:
                self.perf.terminate()
                self.perf.wait()

    def stop(self):
        self.done.set()
        self.join()


# ---------------------------------------------------------------- one block

def fresh_directory(run_dir, case):
    directory, number = run_dir / 'runs' / case, 2
    while directory.exists():
        directory, number = run_dir / 'runs' / ('%s-%d' % (case, number)), number + 1
    directory.mkdir(parents=True)
    return directory


def save_leftovers(member, directory, run_name, bench_head, bank):
    """Save the exported leftover goals (pure statements) with tools/save_goal.py."""
    goals = [leftover for leftover in R.load_block(directory)['leftovers'] if leftover.get('statement')]
    if not goals:
        return None
    folder = directory / 'leftover'
    folder.mkdir(exist_ok=True)
    files = []
    for index, goal in enumerate(goals, 1):
        path = folder / ('Goal%02d.v' % index)
        path.write_text('(* %s goal, class "%s", counts %s *)\nGoal %s.\n'
                        % (goal['kind'], goal['class'], json.dumps(goal['counts']), goal['statement']))
        files.append(str(path))
    result = subprocess.run([sys.executable, str(TOOLS / 'save_goal.py'), '--function', member['function'],
                             '--case', member['case'], '--tag', 'bench-' + run_name, '--head', bench_head,
                             '--bank', str(bank), '--command', 'tools/bench/bench.py run', *files],
                            capture_output=True, text=True, cwd=TOOLS)
    return result.stdout.strip() if result.returncode == 0 else 'save_goal failed: ' + result.stderr.strip()


def dump_caller_text(text):
    """The caller with its closing `Qed.` replaced by `Show.` and `Abort.`: the proof script up to
    the end is unchanged, so compiling it prints the goals zesu_block2 leaves. None without a `Qed.`."""
    match = re.search(r'\nQed\.\s*\Z', text)
    return None if match is None else text[:match.start()] + '\nShow.\nAbort.\n'


GOAL_COUNT = re.compile(r'^(\d+) goals?\b.*$', re.M)


def final_goals(log):
    """The goal text `Show.` printed: from the last `N goal(s)` line to the end, without the `-time`
    lines of the closing sentences. None if no goal was printed."""
    starts = list(GOAL_COUNT.finditer(log))
    if not starts:
        return None
    lines = log[starts[-1].start():].splitlines()
    return '\n'.join(line for line in lines if not line.startswith('Chars ')).rstrip() + '\n'


def dump_leftover(member, directory, caller, context, caps, run_name):
    """--dump-leftover: when the block ended on a goal the export skips (a spatial goal prints only
    `@@X skip final spatial`), compile a scratch copy of the caller whose `Qed.` is `Show. Abort.`
    under the same caps and save the printed goals as leftover/FINAL-GOAL.txt. Rules and the
    generated caller are untouched; the copy is never committed. Returns the file, or why none."""
    if not any(leftover.get('status') == 'skip' for leftover in R.load_block(directory)['leftovers']):
        return None
    text = dump_caller_text(caller.read_text())
    if text is None:
        return 'no dump: the caller has no closing Qed.'
    dump = directory / 'leftover' / 'dump'
    dump.mkdir(parents=True, exist_ok=True)
    source = dump / caller.name   # same file name, so the same logical module name
    source.write_text(text)
    C.compile_caller(member['case'], source, context['bank'], dump, caps['limit_gib'], caps['cpu_seconds'],
                     name='bench-%s-%s-dump' % (run_name, member['case']), claim_gib=member.get('claim_gib'))
    log = dump / 'measure.json.log'
    goals = final_goals(log.read_text(errors='replace')) if log.is_file() else None
    if goals is None:
        return 'no dump: the diagnostic compile printed no goal (%s)' % log
    output = directory / 'leftover' / 'FINAL-GOAL.txt'
    output.write_text(goals)
    return str(output)


def run_member(member, options, context):
    directory = fresh_directory(options.run_dir, member['case'])
    caller = directory / ('Caller%s.v' % member['case'])
    caller.write_bytes(subprocess.run(['git', '-C', str(context['workspace']), 'cat-file', 'blob',
                                       '%s:%s' % (context['bench_head'], caller_path(member))],
                                      capture_output=True, check=True).stdout)
    caps = R.member_caps(context['caps'], member)
    sampler = Sampler(directory, caller)
    sampler.start()
    start = time.monotonic()
    try:
        guard_exit = C.compile_caller(member['case'], caller, context['bank'], directory, caps['limit_gib'],
                                      caps['cpu_seconds'], name='bench-%s-%s' % (options.run_dir.name, member['case']),
                                      claim_gib=member.get('claim_gib'))
    finally:
        sampler.stop()
    record = C.verdict(member['case'], caller, context['bank'], directory / 'measure.json', out=directory)
    saved = save_leftovers(member, directory, options.run_dir.name, context['bench_head'], context['bank'])
    dumped = (dump_leftover(member, directory, caller, context, caps, options.run_dir.name)
              if options.dump_leftover is True and record['verdict'] != 'CLOSED' else None)
    row = {'key': R.member_key(member), 'function': member['function'], 'case': member['case'],
           'label': member.get('label'), 'dir': str(directory), 'verdict': record['verdict'],
           'reason': record.get('reason'), 'coqc_rc': record.get('coqc_returncode'), 'guard_exit': guard_exit,
           'cpu_seconds': record.get('cpu_seconds'), 'peak_gib': record.get('peak_gib'),
           'instructions_u': R.instructions(directory / 'perf.csv'), 'wall_seconds': round(time.monotonic() - start),
           'leftovers_saved': saved, 'leftover_dump': dumped, 'ended_utc': now()}
    with ROWS_LOCK:
        with (options.run_dir / 'results.jsonl').open('a') as rows:
            rows.write(json.dumps(row) + '\n')
        print(C.done_line(record), 'key=%s cpu=%s peak=%s' % (row['key'], row['cpu_seconds'], row['peak_gib']),
              flush=True)
    return row


# ---------------------------------------------------------------- commands

def command_run(options):
    bench_set = load_set(options.set)
    root = repo_root()
    head = git(root, 'rev-parse', '--verify', options.head + '^{commit}')
    rules = git(root, 'rev-parse', '--verify', options.rules_commit + '^{commit}') if options.rules_commit else None
    members = [member for member in bench_set['members'] if not options.only or member['case'] in options.only
               or member.get('label') in options.only]
    functions = {member['function'] for member in members}
    overlays = [overlay for overlay in bench_set.get('overlays', []) if overlay['name'] in functions]
    run_dir = options.run_dir = options.run_dir.resolve()
    run_dir.mkdir(parents=True, exist_ok=True)

    def log(message):
        print('%s %s' % (now()[:19] + 'Z', message), flush=True)

    key, workspace, bench_head = prepare_workspace(root, head, rules, overlays)
    try:
        return run_in_workspace(options, bench_set, members, overlays, head, rules, run_dir, log,
                                key, workspace, bench_head)
    finally:
        if options.keep_bank:
            log('workspace %s and its bank kept for reuse (--keep-bank)' % workspace)
        else:
            rc = J.main(['remove-worktree', str(workspace)])
            log('workspace %s %s' % (workspace, 'removed' if rc == 0 else 'kept: remove-worktree refused'))


def run_in_workspace(options, bench_set, members, overlays, head, rules, run_dir, log, key, workspace, bench_head):
    log('workspace %s at %s' % (workspace, bench_head[:12]))
    make_vars = {}
    for overlay in overlays:
        make_vars.update(overlay.get('make_vars', {}))
    targets = bank_targets(workspace, bench_head, members)
    bank = build_bank(workspace, key, bench_head, targets, make_vars, log)
    caps = bench_set['caps']
    meta = {'schema': 'bench-run/1', 'set': bench_set['name'], 'set_sha256': hashlib.sha256(
                json.dumps(bench_set, sort_keys=True).encode()).hexdigest(),
            'head': head, 'rules': rules, 'bench_head': bench_head, 'workspace': str(workspace), 'bank': str(bank),
            'overlays': overlays, 'caps': caps, 'members': members,
            'telemetry': not options.no_telemetry, 'callers': options.callers and not options.no_telemetry,
            'jobs': options.jobs or bench_set.get('jobs', 6),
            'started_utc': now(), 'tool_sha256': C.sha256(__file__)}
    (run_dir / 'RUN.json').write_text(json.dumps(meta, indent=1) + '\n')
    if not (run_dir / 'ITEM.json').exists():
        (run_dir / 'ITEM.json').write_text(json.dumps({'branch': 'bench/' + key, 'head': bench_head}) + '\n')
    os.environ['OCAMLPATH'] = str(bank / 'install/default/lib')
    os.environ['PATH'] = os.pathsep.join([str(ISLARIS / '_opam/bin'), os.environ.get('PATH', '')])
    if meta['telemetry']:
        os.environ['ZESU_TELEMETRY'] = '1'
    else:
        os.environ.pop('ZESU_TELEMETRY', None)
    if meta['callers']:
        os.environ['ZESU_TELEMETRY_CALLERS'] = '1'
    else:
        os.environ.pop('ZESU_TELEMETRY_CALLERS', None)
    context = {'workspace': workspace, 'bench_head': bench_head, 'bank': bank, 'caps': caps}
    ordered = sorted(members, key=lambda member: -member.get('expected_cpu', 0))
    with ThreadPoolExecutor(max_workers=meta['jobs']) as pool:
        rows = list(pool.map(lambda member: run_member(member, options, context), ordered))
    meta['ended_utc'] = now()
    (run_dir / 'RUN.json').write_text(json.dumps(meta, indent=1) + '\n')
    report = R.render(R.load_run(run_dir))
    (run_dir / 'REPORT.md').write_text(report)
    log('BENCH-DONE %s closed %d of %d at %s' % (bench_set['name'], sum(row['verdict'] == 'CLOSED' for row in rows),
                                                 len(rows), bench_head[:12]))
    return 0


def command_report(options):
    run = R.load_run(options.run)
    base = R.load_run(options.base) if options.base else None
    text = R.render(run, base)
    run_dir = Path(options.run)
    suffix = '-vs-' + Path(options.base).name if options.base else ''
    (run_dir / ('REPORT%s.md' % suffix)).write_text(text)
    (run_dir / ('REPORT%s.json' % suffix)).write_text(json.dumps(R.report_json(run), indent=1, default=str) + '\n')
    print(json.dumps(R.report_json(run), indent=1, default=str) if options.json else text, end='')
    return 0


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    commands = parser.add_subparsers(dest='command', required=True)
    run = commands.add_parser('run', help='run a set')
    run.add_argument('--set', required=True, help='set name under tools/bench/sets, or a JSON path')
    run.add_argument('--head', required=True)
    run.add_argument('--rules-commit')
    run.add_argument('--run-dir', type=Path, required=True)
    run.add_argument('--jobs', type=int)
    run.add_argument('--no-telemetry', action='store_true')
    run.add_argument('--callers', action='store_true',
                     help='also record each solver call\'s Ltac caller (diagnostic; Ltac Backtrace slows it)')
    run.add_argument('--dump-leftover', action='store_true',
                     help='for a block that ends on a goal the export skips (spatial), compile a scratch copy '
                          'of the caller ending in `Show. Abort.` and save the goals (leftover/FINAL-GOAL.txt)')
    run.add_argument('--only', nargs='+', help='run only these cases (case or label)')
    run.add_argument('--keep-bank', action='store_true',
                     help='keep the worktree and its bank for a rerun on the same inputs (default: '
                          'remove them when the run ends)')
    report = commands.add_parser('report', help='report one run')
    report.add_argument('run', type=Path)
    report.add_argument('--base', type=Path)
    report.add_argument('--json', action='store_true')
    options = parser.parse_args(argv)
    return command_run(options) if options.command == 'run' else command_report(options)


if __name__ == '__main__':
    sys.exit(main())
