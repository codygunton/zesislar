"""Early verdict for diagnostic and held-out block sweeps. Never for production gates.

A block compile that will not close used to run for hours, to the sweep's 2 h wall stop or to the
16 GiB memory fence. This module gives a verdict in the sweep harness instead: it watches one block
compile (its guard scope's cgroup and its log) and reports the first budget that the block exceeds.

Budgets come from blocks that closed (`calibrate`). For each function with enough distinct closing
blocks, and for all functions together (the fallback for a function with few or none):

  total     CPU of the whole compile
  zesu_run  CPU before the first `Tactic call zesu_run` line (load plus the first stepping pass)
  post_run  CPU after that line (later passes, finishers, Qed)
  <stage>   CPU of one occurrence of a `@@S stage <name>` marker, until the next marker or the end
            (only for stages that enough distinct closing blocks recorded)

A budget is k times the largest value among closing runs. The memory rule is absolute: anonymous
memory of the scope above rss_gib, which must lie above every closing run.

The stage markers come from a scratch copy of the caller: `with_stage_markers` adds the
redefinition of the diagnostics stage hook (an `idtac`, so the proof is unchanged). The sweep
records each run's stage times in `progress.json`; later calibrations read them.

usage:
  early_verdict.py calibrate --output BUDGETS.json [--k 3] [--rss-gib 12] [--min-blocks 5]
                   [--min-stage-blocks 5] SWEEP_DIR[=FUNCTION]...
  early_verdict.py budget BUDGETS.json FUNCTION
"""
import argparse
import json
import os
from pathlib import Path
import re
import sys
import time

GIB = 2 ** 30
STAGE_MARKER_LINE = 'Ltac ZesuSsz.Automation2.Diagnostics.zesu_diag_stage name ::= idtac "@@S stage" name.'
PASS_LINE = re.compile(r'Tactic call zesu_run ran for [0-9.]+ secs \(([0-9.]+)u,([0-9.]+)s\)')
STAGE_LINE = re.compile(r'@@S stage "?([^"\s]+)"?')
FENCE_KILL_MARK = 'memory fence kill'
# CPU before the first pass that the first pass line does not report (loading the
# imports). Measured on the decodeItem sweeps: at most 28 s (2026-11-13).
LOAD_ALLOWANCE = 30.0
RUN, POST = 'zesu_run', 'post_run'


def with_stage_markers(text):
    """Return a caller's text with the stage hook redefinition before its first declaration."""
    if STAGE_MARKER_LINE in text:
        return text
    match = re.search(r'(?m)^(Definition|Lemma|Theorem) ', text)
    if match is None or 'ZesuSsz.Automation2.All' not in text[:match.start()]:
        raise ValueError('no declaration after the Automation2 import')
    return text[:match.start()] + STAGE_MARKER_LINE + '\n\n' + text[match.start():]


# Budgets.

def _maxima():
    return {'closers': 0, 'blocks': [], 'cpu': 0.0, 'run': 0.0, 'post': 0.0, 'rss_gib': 0.0, 'stages': {}}


def _add(maxima, case, closer):
    """Fold one closing run of block `case` into the maxima."""
    maxima['closers'] += 1
    if case not in maxima['blocks']:
        maxima['blocks'] = sorted(maxima['blocks'] + [case])
    for key in ('cpu', 'run', 'post', 'rss_gib'):
        maxima[key] = round(max(maxima[key], closer[key]), 1)
    for name, value in closer['stages'].items():
        stage = maxima['stages'].setdefault(name, {'max': 0.0, 'blocks': []})
        stage['max'] = round(max(stage['max'], value), 1)
        if case not in stage['blocks']:
            stage['blocks'] = sorted(stage['blocks'] + [case])


def closer_record(run_dir):
    """Stage values of one run directory, or None when the run did not close."""
    run_dir = Path(run_dir)
    measure, log = run_dir / 'measure.json', run_dir / 'run.log'
    if not measure.exists() or not log.exists():
        return None
    data = json.loads(measure.read_text())
    text = log.read_text(errors='replace')
    if data.get('returncode') != 0 or FENCE_KILL_MARK in text:
        return None
    cpu = data['cpu_user'] + data['cpu_sys']
    record = {'cpu': cpu, 'rss_gib': data['max_rss_kib'] / 2 ** 20, 'stages': {}}
    progress = run_dir / 'progress.json'
    if progress.exists():
        recorded = json.loads(progress.read_text())
        run = recorded.get('run_cpu')
        record['run'] = cpu if run is None else run
        record['post'] = 0.0 if run is None else cpu - run
        record['stages'] = recorded.get('stage_max', {})
        return record
    first = PASS_LINE.search(text)
    if first is None:
        record['run'], record['post'] = cpu, 0.0
    else:
        first_pass = float(first.group(1)) + float(first.group(2))
        record['run'] = first_pass + LOAD_ALLOWANCE
        record['post'] = cpu - first_pass  # still holds the load: an upper bound
    return record


def sweep_functions(sweep_dir, default=None):
    """Map case to function from the sweep's CALLERS-*.json rows."""
    functions = {}
    for table in sorted(Path(sweep_dir).glob('CALLERS*.json')):
        for row in json.loads(table.read_text()):
            if isinstance(row, dict) and 'case' in row:
                functions[row['case']] = row.get('function') or default
    return functions


def calibrate(sweeps, k=3.0, rss_gib=12.0, min_blocks=5, min_stage_blocks=5):
    """Budgets from the closing runs of sweep directories. sweeps: [(dir, default function or None)].

    A function gets its own budgets only when at least min_blocks distinct blocks of it closed:
    repeated runs of one or two blocks across columns do not describe the function's other blocks."""
    functions, overall = {}, _maxima()
    for sweep_dir, default in sweeps:
        names = sweep_functions(sweep_dir, default)
        for run_dir in sorted(Path(sweep_dir).glob('runs/*')):
            case = run_dir.name.split('-')[0]
            function = names.get(case, default)
            if function is None:
                raise ValueError('no function for %s: name it as DIR=FUNCTION' % run_dir)
            record = closer_record(run_dir)
            if record is not None:
                _add(functions.setdefault(function, _maxima()), case, record)
                _add(overall, '%s:%s' % (function, case), record)
    if overall['closers'] == 0:
        raise ValueError('no closing runs')
    if rss_gib <= overall['rss_gib']:
        raise ValueError('rss_gib %.1f is not above the largest closing run (%.1f GiB)' % (rss_gib, overall['rss_gib']))
    return {'k': k, 'rss_gib': rss_gib, 'min_blocks': min_blocks, 'min_stage_blocks': min_stage_blocks,
            'generated': time.strftime('%Y-%m-%dT%H:%M:%SZ', time.gmtime()),
            'sweeps': [str(d) for d, _ in sweeps], 'functions': functions, 'global': overall}


def budget(budgets, function):
    """CPU budgets (seconds) and memory limit (bytes) for one function's blocks."""
    maxima = budgets['functions'].get(function)
    scope = 'function'
    if maxima is None or len(maxima['blocks']) < budgets['min_blocks']:
        maxima, scope = budgets['global'], 'global'
    k = budgets['k']
    stages = {name: k * stage['max'] for name, stage in maxima['stages'].items()
              if len(stage['blocks']) >= budgets['min_stage_blocks'] and name not in (RUN, POST)}
    return {'function': function, 'scope': scope, 'k': k, 'total': k * maxima['cpu'], RUN: k * maxima['run'],
            POST: k * maxima['post'], 'stages': stages, 'rss_bytes': int(budgets['rss_gib'] * GIB)}


# Sampling one block's scope.

def _children(pid):
    children = []
    for task in Path('/proc/%d/task' % pid).glob('*/children'):
        try:
            children += [int(x) for x in task.read_text().split()]
        except OSError:
            pass
    return children


def descendants(pid):
    found, todo = [], [pid]
    while todo:
        current = todo.pop()
        found.append(current)
        todo += _children(current)
    return found


def cgroup_of(pid):
    """The cgroup v2 path of a process, or None once it is gone."""
    try:
        return Path('/proc/%d/cgroup' % pid).read_text().strip().splitlines()[-1].split(':', 2)[2]
    except (OSError, IndexError):
        return None


# A block's guard scope: zesudet-<name>-<pid>-<n>.scope. A batch scope (zesudet-batch-<name>-<pid>.scope)
# holds the sweep driver and the guard process until systemd starts the block's own scope.
BLOCK_SCOPE = re.compile(r'/zesudet-(?!batch-)[^/]*-\d+-\d+\.scope$')


def scope_cgroup(pid, root=Path('/sys/fs/cgroup')):
    """The cgroup directory of the guard scope under pid's process tree, or None before it starts."""
    own = cgroup_of(os.getpid())
    for member in descendants(pid):
        path = cgroup_of(member)
        if path and path != own and BLOCK_SCOPE.search(path):
            return root / path.lstrip('/')
    return None


def read_cgroup(directory):
    """(CPU seconds, anonymous memory bytes) of a cgroup, or None once it is gone."""
    try:
        cpu = memory = None
        for line in (directory / 'cpu.stat').read_text().splitlines():
            if line.startswith('usage_usec '):
                cpu = int(line.split()[1]) / 1e6
        for line in (directory / 'memory.stat').read_text().splitlines():
            if line.startswith('anon '):
                memory = int(line.split()[1])
        return None if cpu is None or memory is None else (cpu, memory)
    except OSError:
        return None


class Monitor:
    """Watch one block compile. poll() returns a verdict dict once a budget is exceeded."""

    def __init__(self, limits, log_path, pid, sample=None):
        self.limits, self.log_path, self.pid = limits, Path(log_path), pid
        self.sample = sample or self._sample_scope
        self.cgroup, self.offset, self.partial = None, 0, ''
        self.cpu = self.memory = 0.0
        self.run_cpu = None                  # CPU at the first pass line
        self.stage, self.stage_start = None, 0.0
        self.stage_cpu, self.stage_max, self.events = {}, {}, []
        self.verdict = None

    def _sample_scope(self):
        if self.cgroup is None:
            self.cgroup = scope_cgroup(self.pid)
            if self.cgroup is None:
                return None
        return read_cgroup(self.cgroup)

    def _close_stage(self):
        if self.stage is not None:
            spent = self.cpu - self.stage_start
            self.stage_cpu[self.stage] = round(self.stage_cpu.get(self.stage, 0.0) + spent, 1)
            self.stage_max[self.stage] = round(max(self.stage_max.get(self.stage, 0.0), spent), 1)

    def _line(self, line):
        if PASS_LINE.search(line):
            if self.run_cpu is None:
                self.run_cpu = round(self.cpu, 1)
            self.events.append([round(self.cpu, 1), RUN])
            self._close_stage()
            self.stage = None
            return
        match = STAGE_LINE.search(line)
        if match:
            self._close_stage()
            self.stage, self.stage_start = match.group(1), self.cpu
            self.events.append([round(self.cpu, 1), match.group(1)])

    def _read_log(self):
        try:
            with self.log_path.open('rb') as handle:
                handle.seek(self.offset)
                chunk = handle.read()
        except OSError:
            return
        self.offset += len(chunk)
        lines = (self.partial + chunk.decode(errors='replace')).split('\n')
        self.partial = lines.pop()
        for line in lines:
            self._line(line)

    def current_stage(self):
        if self.stage is not None:
            return self.stage
        return RUN if self.run_cpu is None else POST

    def check(self):
        """The first exceeded limit at the current sample, or None."""
        limits, stage = self.limits, self.current_stage()
        tests = [('memory', self.memory, limits['rss_bytes'])]
        if self.stage is not None and self.stage in limits['stages']:
            tests.append(('stage', self.cpu - self.stage_start, limits['stages'][self.stage]))
        if self.run_cpu is None:
            tests.append((RUN, self.cpu, limits[RUN]))
        else:
            tests.append((POST, self.cpu - self.run_cpu, limits[POST]))
        tests.append(('total', self.cpu, limits['total']))
        for rule, value, limit in tests:
            if value > limit:
                unit = GIB if rule == 'memory' else 1
                return {'rule': rule, 'stage': stage, 'value': round(value / unit, 1), 'limit': round(limit / unit, 1),
                        'cpu': round(self.cpu, 1), 'rss_gib': round(self.memory / GIB, 2),
                        'scope': limits['scope'], 'k': limits['k']}
        return None

    def poll(self):
        sample = self.sample()
        if sample is None:
            return self.verdict
        self.cpu, self.memory = sample
        self._read_log()
        if self.verdict is None:
            self.verdict = self.check()
        return self.verdict

    def summary(self):
        """Stage record of the run (written to progress.json)."""
        self._read_log()
        stage_cpu, stage_max = dict(self.stage_cpu), dict(self.stage_max)
        if self.stage is not None:
            spent = self.cpu - self.stage_start
            stage_cpu[self.stage] = round(stage_cpu.get(self.stage, 0.0) + spent, 1)
            stage_max[self.stage] = round(max(stage_max.get(self.stage, 0.0), spent), 1)
        return {'cpu': round(self.cpu, 1), 'rss_gib': round(self.memory / GIB, 2), 'run_cpu': self.run_cpu,
                'stage_cpu': stage_cpu, 'stage_max': stage_max, 'events': self.events, 'verdict': self.verdict,
                'limits': self.limits}


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = parser.add_subparsers(dest='command', required=True)
    cal = sub.add_parser('calibrate')
    cal.add_argument('--output', type=Path, required=True)
    cal.add_argument('--k', type=float, default=3.0)
    cal.add_argument('--rss-gib', type=float, default=12.0)
    cal.add_argument('--min-blocks', type=int, default=5)
    cal.add_argument('--min-stage-blocks', type=int, default=5)
    cal.add_argument('sweeps', nargs='+')
    show = sub.add_parser('budget')
    show.add_argument('budgets', type=Path)
    show.add_argument('function')
    options = parser.parse_args(argv)
    if options.command == 'budget':
        print(json.dumps(budget(json.loads(options.budgets.read_text()), options.function), indent=1))
        return 0
    sweeps = []
    for item in options.sweeps:
        directory, _, function = item.partition('=')
        sweeps.append((Path(directory), function or None))
    budgets = calibrate(sweeps, options.k, options.rss_gib, options.min_blocks, options.min_stage_blocks)
    temporary = options.output.with_name(options.output.name + '.tmp')
    temporary.write_text(json.dumps(budgets, indent=1) + '\n')
    os.replace(temporary, options.output)
    print(json.dumps({name: [m['closers'], len(m['blocks'])] for name, m in budgets['functions'].items()}))
    return 0


if __name__ == '__main__':
    sys.exit(main())
