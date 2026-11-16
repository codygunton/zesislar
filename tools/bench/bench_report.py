"""Parse one BENCH run and render its report (see bench.py report).

A block's run directory (RUN/runs/<case>) holds what bench.py run wrote:
  measure.json, measure.json.log   tools/measure.py record and coqc's output (with -time)
  CLOSURE.json | NOT-CLOSED.json   tools/closure_cert.py verdict
  samples.jsonl                    the external 1 s sampler: {"t", "rss_kib", "cpu_s", "log_bytes"}
  perf.csv                         `perf stat -x, -e instructions:u -p <coqc>` output
  run.log                          the resource guard's output

Log lines the parser reads:
  Chars A - B [cmd] T secs (Uu,Ss)            coqc -time record of one sentence
  Tactic call zesu_run ran for T secs (Uu,Ss) (success|failure ...)
  @@T kind=<k> site=<s> stage=<s> facts=<n> nodes=<n> goal_nodes=<n> ms=<n> ok=<0|1> cpu_ms=<n>
      ts_us=<n> rss0_kb=<n> rss1_kb=<n>      one solver call, printed at its end (ZESU_TELEMETRY=1);
                                              values bare or "quoted"; -1 counts mean "not one goal"
  @@T kind=stage site=<stage> ms=... cpu_ms=...   one stage, printed at its end (nested stages
                                              include their children; zesu_run_pass lines count steps)
  @@X begin <kind> / binders / counts / stmt <source> / end, @@X skip <kind> <why>
                                              goal export records (ResidualExport.v); `final` records
                                              are the goals open at the end of zesu_block2
  @@S stage "<stage>"                         diagnostics stage marker (stage entry)
Coq wraps long messages; lines that continue an @@ record are joined to it.

A call without rss0_kb/rss1_kb is joined to memory by its byte offset in the log: the first sampler
row whose log_bytes covers the record's end gives its arrival time, CPU and RSS; its RSS before is
the row at (arrival - its duration). The sampler's resolution is 1 s.
"""
from collections import defaultdict
import bisect
import json
from pathlib import Path
import re

CHARS = re.compile(r'^Chars (\d+) - (\d+) \[(.*)\] ([0-9.]+) secs \(([0-9.]+)u,([0-9.]+)s\)')
ZESU_RUN = re.compile(r'^Tactic call zesu_run ran for ([0-9.]+) secs \(([0-9.]+)u,([0-9.]+)s\) \((success|failure)')
DIAG_STAGE = re.compile(r'^@@S stage "?([^"\s]+)"?')
TOKEN = re.compile(r'([A-Za-z_][\w.-]*)=("(?:[^"\\]|\\.)*"|\S*)|("(?:[^"\\]|\\.)*"|\S+)')
ERROR = re.compile(r'^File "[^"]*", line (\d+), characters (\d+)-(\d+):')
NOT_CONTINUATION = ('@@', 'Chars ', 'Tactic call ', 'File ', 'Warning:', 'Error:', 'live-memory')
RELATIONS = re.compile(r'(<=|>=|<>|≠|≤|≥|<|>|=)')
ALIASES = {
    'kind': ('kind', 'solver', 'tactic'),
    'stage': ('stage', 'phase'),
    'site': ('site', 'at', 'origin'),
    'facts': ('facts', 'ctx_facts', 'context_facts', 'hyps'),
    'nodes': ('nodes', 'ctx_nodes', 'context_nodes'),
    'goal': ('goal_nodes', 'goal', 'goal_size'),
    'seconds': ('secs', 'seconds', 'time', 'dt'),
    'ms': ('ms', 'millis'),
    'cpu_ms': ('cpu_ms',),
    'ok': ('ok', 'success', 'result', 'solved'),
    'rss0': ('rss0_kb', 'rss0_kib'),
    'rss1': ('rss1_kb', 'rss1_kib'),
    'ts': ('ts_us',),
}
TRUE = {'1', 'true', 'ok', 'yes', 'success', 'solved'}


# ---------------------------------------------------------------- parsing one log

def scalar(text):
    if len(text) >= 2 and text[0] == text[-1] == '"':
        return text[1:-1].replace('\\"', '"').replace('\\\\', '\\')
    for convert in (int, float):
        try:
            return convert(text)
        except ValueError:
            pass
    return text


def telemetry_fields(rest):
    """`[kind] key=value ...` -> dict; a leading bare token is the kind when no kind= is given."""
    fields, bare = {}, []
    for match in TOKEN.finditer(rest):
        if match.group(1):
            fields[match.group(1)] = scalar(match.group(2))
        else:
            bare.append(scalar(match.group(3)))
    if bare and 'kind' not in fields:
        fields['kind'] = bare.pop(0)
    if bare:
        fields['args'] = bare
    return fields


def pick(fields, name):
    for key in ALIASES[name]:
        if key in fields:
            return fields[key]
    return None


def count(value):
    return None if not isinstance(value, (int, float)) or value < 0 else value


def solver_call(fields):
    """Normalize one telemetry record: kind/stage/site/facts/nodes/goal/seconds/cpu/ok/rss/start."""
    seconds = pick(fields, 'seconds')
    if seconds is None and pick(fields, 'ms') is not None:
        seconds = pick(fields, 'ms') / 1000
    cpu = pick(fields, 'cpu_ms')
    cpu = cpu / 1000 if isinstance(cpu, (int, float)) else seconds
    ok = pick(fields, 'ok')
    if ok is not None:
        ok = str(ok).lower() in TRUE
    start = pick(fields, 'ts')
    return {'kind': str(pick(fields, 'kind')), 'stage': pick(fields, 'stage'), 'site': pick(fields, 'site'),
            'facts': count(pick(fields, 'facts')), 'nodes': count(pick(fields, 'nodes')),
            'goal': count(pick(fields, 'goal')), 'seconds': seconds, 'cpu': cpu, 'ok': ok,
            'rss_before_kib': count(pick(fields, 'rss0')), 'rss_after_kib': count(pick(fields, 'rss1')),
            'start_t': start / 1e6 if isinstance(start, (int, float)) else None}


def records(text):
    """(line, end offset) per logical line: wrapped continuation lines join the @@ record before them."""
    current, offset = None, 0
    for raw in text.splitlines(keepends=True):
        offset += len(raw.encode())
        line = raw.rstrip('\n')
        if current is not None and line.strip() and not line.startswith(NOT_CONTINUATION):
            current[0] += ' ' + line.strip()
            current[1] = offset
            continue
        if current is not None:
            yield tuple(current)
            current = None
        if line.startswith('@@'):
            current = [line, offset]
        else:
            yield line, offset
    if current is not None:
        yield tuple(current)


def goal_class(kind, statement):
    """A coarse class of an exported goal: its kind, the conclusion's relation and left head."""
    depth, last, index = 0, 0, 0
    while index < len(statement):  # the conclusion follows the last top-level arrow or comma
        char = statement[index]
        depth += char in '([{'
        depth -= char in ')]}'
        if depth == 0 and (statement.startswith('->', index) or statement.startswith('→', index)):
            last = index + (2 if statement.startswith('->', index) else 1)
        elif depth == 0 and char == ',':
            last = index + 1
        index += 1
    conclusion = statement[last:].strip()
    relation = RELATIONS.search(conclusion)
    left = conclusion[:relation.start()] if relation else conclusion
    head = (re.findall(r"[A-Za-z_][\w.']*", left) or ['?'])[0]
    return '%s %s %s' % (kind, relation.group(1) if relation else 'prop', head)


def parse_log(text):
    """Events of one coqc log, each with the byte offset just past its record ('end')."""
    out = {'commands': [], 'zesu_runs': [], 'markers': [], 'stage_records': [], 'calls': [], 'exports': [],
           'errors': [], 'events': 0}
    export, error = None, None
    for line, offset in records(text):
        if error is not None:
            if line.startswith(NOT_CONTINUATION[:3]):
                out['errors'].append(error)
                error = None
            else:
                error['text'] += line + '\n'
                continue
        if match := CHARS.match(line):
            out['commands'].append({'start': int(match[1]), 'stop': int(match[2]), 'command': match[3],
                                    'seconds': float(match[5]) + float(match[6]), 'end': offset})
        elif match := ZESU_RUN.match(line):
            out['zesu_runs'].append({'seconds': float(match[2]) + float(match[3]), 'ok': match[4] == 'success',
                                     'end': offset})
        elif match := DIAG_STAGE.match(line):
            out['markers'].append({'name': match[1], 'end': offset})
        elif line.startswith('@@T '):
            out['events'] += 1
            fields = telemetry_fields(line[4:])
            call = dict(solver_call(fields), end=offset, fields=fields)
            out['stage_records' if call['kind'] == 'stage' else 'calls'].append(call)
        elif line.startswith('@@X '):
            body = line[4:]
            if body.startswith('skip '):
                parts = body.split(' ', 2)
                out['exports'].append({'kind': parts[1], 'status': 'skip', 'reason': parts[2] if len(parts) > 2 else '',
                                       'class': '%s skip: %s' % (parts[1], parts[2] if len(parts) > 2 else '?'),
                                       'end': offset})
            elif body.startswith('begin '):
                export = {'kind': body[6:].strip(), 'status': 'pure', 'counts': {}, 'statement': None, 'end': offset}
            elif export is not None and body.startswith('counts '):
                export['counts'] = dict(item.split('=', 1) for item in body.split()[1:] if '=' in item)
            elif export is not None and body.startswith('stmt '):
                export['statement'] = body[5:].strip()
            elif export is not None and body.strip() == 'end':
                if export['statement']:
                    export['class'] = goal_class(export['kind'], export['statement'])
                    out['exports'].append(dict(export, end=offset))
                export = None
        elif match := ERROR.match(line):
            error = {'line': int(match[1]), 'text': '', 'end': offset}
    if error is not None:
        out['errors'].append(error)
    return out


def leftovers(parsed, closed):
    """The goals left open: `final` export records; a run without them that did not close gives
    its `split` records (killed or stopped before the end of zesu_block2)."""
    finals = [record for record in parsed['exports'] if record['kind'] == 'final']
    if finals or closed:
        return finals
    return [record for record in parsed['exports'] if record['kind'] == 'split']


def command_class(command):
    text = command.replace('~', ' ').strip()
    if text.startswith(('Require', 'From', 'Import', 'Export')):
        return 'imports'
    if text.startswith('Qed'):
        return 'qed'
    if text.startswith('Print Assumptions'):
        return 'assumptions'
    if 'zesu_block2' in text or text.startswith('zesu_'):
        return 'proof'
    return 'declarations'


# ---------------------------------------------------------------- samples

def read_samples(path):
    path = Path(path)
    if not path.is_file():
        return []
    rows = []
    for line in path.read_text().splitlines():
        try:
            rows.append(json.loads(line))
        except ValueError:
            continue  # a killed sampler can leave a partial last line
    return rows


class Timeline:
    """Sampler rows, searchable by log offset and by time."""

    def __init__(self, samples):
        self.samples = [row for row in samples if row.get('log_bytes') is not None]
        self.bytes = [row['log_bytes'] for row in self.samples]
        self.times = [row['t'] for row in self.samples]

    def __bool__(self):
        return bool(self.samples)

    def at_offset(self, end):
        index = bisect.bisect_left(self.bytes, end)
        return self.samples[index] if index < len(self.samples) else (self.samples[-1] if self.samples else None)

    def at_time(self, moment):
        index = bisect.bisect_right(self.times, moment) - 1
        return self.samples[max(index, 0)] if self.samples else None


def join_calls(calls, timeline):
    """Fill t, cpu_s and the RSS before/after of each call: the telemetry's own rss0/rss1 when it
    printed them, else the sampler rows at the record's arrival and at (arrival - its duration)."""
    for call in calls:
        call.update(t=None, cpu_s=None, rss_growth_kib=None)
        after = timeline.at_offset(call['end']) if timeline else None
        if after is not None:
            call.update(t=after['t'], cpu_s=after.get('cpu_s'))
            if call['rss_after_kib'] is None or call['rss_before_kib'] is None:
                before = timeline.at_time(after['t'] - (call['seconds'] or 0) - 1e-9)
                call.update(rss_after_kib=after.get('rss_kib'), rss_before_kib=before.get('rss_kib'))
        if call['rss_after_kib'] is not None and call['rss_before_kib'] is not None:
            call['rss_growth_kib'] = call['rss_after_kib'] - call['rss_before_kib']
    return calls


def stage_times(parsed, timeline, total_cpu):
    """{stage: {"cpu": s, "steps": n, "rss_growth_kib": k}}: from telemetry stage records (a stage
    includes its nested stages), else from @@S markers and the samples, else from -time and zesu_run."""
    stages = {}
    if parsed['stage_records']:
        for record in parsed['stage_records']:
            entry = stages.setdefault(str(record['site']), {'cpu': 0.0, 'steps': 0, 'rss_growth_kib': None})
            entry['cpu'] += record['cpu'] or 0
            entry['steps'] += 1
            if record['rss_after_kib'] is not None and record['rss_before_kib'] is not None:
                entry['rss_growth_kib'] = (entry['rss_growth_kib'] or 0) + max(
                    record['rss_after_kib'] - record['rss_before_kib'], 0)
        return {name: dict(value, cpu=round(value['cpu'], 1)) for name, value in stages.items()}
    marks = parsed['markers']
    if marks and timeline:
        points = [(mark, timeline.at_offset(mark['end'])) for mark in marks]
        for index, (mark, sample) in enumerate(points):
            if index + 1 < len(points):
                following = points[index + 1][1]
            else:
                following = {'cpu_s': total_cpu, 'rss_kib': timeline.samples[-1].get('rss_kib')}
            entry = stages.setdefault(mark['name'], {'cpu': 0.0, 'steps': 0, 'rss_growth_kib': 0})
            if sample.get('cpu_s') is not None and following.get('cpu_s') is not None:
                entry['cpu'] += max(following['cpu_s'] - sample['cpu_s'], 0.0)
            if sample.get('rss_kib') is not None and following.get('rss_kib') is not None:
                entry['rss_growth_kib'] += max(following['rss_kib'] - sample['rss_kib'], 0)
            entry['steps'] += 1
        return {name: dict(value, cpu=round(value['cpu'], 1)) for name, value in stages.items()}
    if marks:  # markers without samples: counts only
        for mark in marks:
            stages.setdefault(mark['name'], {'cpu': None, 'steps': 0, 'rss_growth_kib': None})['steps'] += 1
        return stages
    for command in parsed['commands']:
        entry = stages.setdefault(command_class(command['command']), {'cpu': 0.0, 'steps': 0, 'rss_growth_kib': None})
        entry['cpu'] += command['seconds']
        entry['steps'] += 1
    if parsed['zesu_runs']:
        stages['proof.zesu_run'] = {'cpu': sum(run['seconds'] for run in parsed['zesu_runs']),
                                    'steps': len(parsed['zesu_runs']), 'rss_growth_kib': None}
    if 'proof' not in stages and total_cpu is not None:  # the proof never finished: the rest is the proof
        known = sum(entry['cpu'] for name, entry in stages.items() if name != 'proof.zesu_run')
        stages['proof (unfinished)'] = {'cpu': max(total_cpu - known, 0.0), 'steps': 1, 'rss_growth_kib': None}
    return {name: dict(value, cpu=round(value['cpu'], 1)) for name, value in stages.items()}


def stage_reached(parsed, verdict, end):
    if verdict == 'CLOSED':
        return 'closed'
    classes = [command_class(command['command']) for command in parsed['commands']]
    if 'qed' in classes:
        return 'assumptions'
    if 'proof' in classes:
        return 'qed'
    passes = sum(record['site'] == 'zesu_run_pass' for record in parsed['stage_records'])
    last = max(parsed['calls'] + parsed['stage_records'], key=lambda record: record['end'], default=None)
    if last is not None:  # the innermost stage of the last telemetry record
        where = last['site'] if last['kind'] == 'stage' else last['stage'] or 'proof'
        return '%s (%d zesu_run_pass, %s)' % (where, passes, end)
    where = parsed['markers'][-1]['name'] if parsed['markers'] else 'proof'
    runs = len(parsed['zesu_runs'])
    return '%s (%d zesu_run%s, %s)' % (where, runs, '' if runs == 1 else 's', end)


def instructions(path):
    path = Path(path)
    if not path.is_file():
        return None
    for line in path.read_text(errors='replace').splitlines():
        fields = line.split(',')
        if len(fields) > 2 and fields[2].startswith('instructions'):
            try:
                return int(float(fields[0]))
            except ValueError:
                return None
    return None


def run_end(record, measure, guard_text, caps):
    """How the compile ended: closed, failed (coqc error), cpu-cap, memory-fence, killed, no-run."""
    if record.get('verdict') == 'CLOSED':
        return 'closed'
    code = measure.get('returncode') if measure else None
    if measure is None or 'started_utc' not in measure:
        return 'no-run'
    if code is None:
        return 'killed (no exit status)'
    if code > 0:
        return 'failed'
    if code == 0:
        return 'not certified'
    cpu = (measure.get('cpu_user') or 0) + (measure.get('cpu_sys') or 0)
    if caps.get('cpu_seconds') and cpu >= 0.97 * caps['cpu_seconds']:
        return 'cpu-cap'
    if 'fence' in guard_text or (caps.get('limit_gib') and measure.get('max_rss_kib', 0) / 2**20 >= 0.95 * caps['limit_gib']):
        return 'memory-fence'
    return 'killed (signal %d)' % -code


def load_block(directory, caps=None):
    """Everything the report needs about one block run directory."""
    directory = Path(directory)
    caps = caps or {}
    record = {}
    for name in ('CLOSURE.json', 'NOT-CLOSED.json'):
        if (directory / name).is_file():
            record = json.loads((directory / name).read_text())
    measure = json.loads((directory / 'measure.json').read_text()) if (directory / 'measure.json').is_file() else None
    log = directory / 'measure.json.log'
    text = log.read_text(errors='replace') if log.is_file() else ''
    guard_text = (directory / 'run.log').read_text(errors='replace') if (directory / 'run.log').is_file() else ''
    parsed = parse_log(text)
    timeline = Timeline(read_samples(directory / 'samples.jsonl'))
    cpu = None
    if measure and 'cpu_user' in measure:
        cpu = round(measure['cpu_user'] + measure['cpu_sys'], 1)
    elif timeline:
        cpu = timeline.samples[-1].get('cpu_s')
    peak_kib = measure.get('max_rss_kib') if measure else None
    if peak_kib is None and timeline:
        peak_kib = max((row.get('hwm_kib') or row.get('rss_kib') or 0) for row in timeline.samples)
    join_calls(parsed['calls'], timeline)
    join_calls(parsed['stage_records'], timeline)
    end = run_end(record, measure, guard_text, caps)
    verdict = record.get('verdict', 'NO-VERDICT')
    return {
        'dir': str(directory), 'verdict': verdict, 'reason': record.get('reason'), 'end': end,
        'cpu': cpu, 'wall': round(measure['wall'], 1) if measure and 'wall' in measure else None,
        'peak_gib': round(peak_kib / 2**20, 2) if peak_kib else None,
        'instructions': instructions(directory / 'perf.csv'),
        'stage': stage_reached(parsed, verdict, end),
        'stages': stage_times(parsed, timeline, cpu),
        'calls': parsed['calls'], 'telemetry_events': parsed['events'],
        'leftovers': leftovers(parsed, verdict == 'CLOSED'), 'exports': len(parsed['exports']),
        'errors': parsed['errors'], 'samples': len(timeline.samples),
    }


# ---------------------------------------------------------------- one run

def load_run(run_dir):
    """RUN.json plus the last row per member from results.jsonl, each with its parsed block."""
    run_dir = Path(run_dir)
    meta = json.loads((run_dir / 'RUN.json').read_text())
    rows = {}
    if (run_dir / 'results.jsonl').is_file():
        for line in (run_dir / 'results.jsonl').read_text().splitlines():
            if line.strip():
                row = json.loads(line)
                rows[row['key']] = row
    blocks = []
    for member in meta['members']:
        key = member_key(member)
        row = rows.get(key)
        block = load_block(row['dir'], meta.get('caps')) if row else None
        blocks.append({'key': key, 'member': member, 'row': row, 'block': block})
    return {'dir': str(run_dir), 'meta': meta, 'blocks': blocks}


def member_key(member):
    return '%s/%s' % (member['function'], member['case'])


def member_name(member):
    label = member.get('label')
    return '%s %s%s' % (member['function'], member['case'], ' (%s)' % label if label else '')


# ---------------------------------------------------------------- ranking

def ranking(run):
    """CPU and memory per stage, solver kind and site, summed over the set."""
    tables = {'stage': defaultdict(lambda: {'cpu': 0.0, 'rss_growth_kib': 0, 'blocks': set(), 'steps': 0}),
              'kind': defaultdict(lambda: {'cpu': 0.0, 'rss_growth_kib': 0, 'blocks': set(), 'calls': 0, 'failed': 0}),
              'site': defaultdict(lambda: {'cpu': 0.0, 'rss_growth_kib': 0, 'blocks': set(), 'calls': 0, 'failed': 0})}
    for entry in run['blocks']:
        block = entry['block']
        if block is None:
            continue
        for name, stage in block['stages'].items():
            row = tables['stage'][name]
            row['cpu'] += stage['cpu'] or 0
            row['rss_growth_kib'] += stage['rss_growth_kib'] or 0
            row['steps'] += stage['steps'] or 0
            row['blocks'].add(entry['key'])
        for call in block['calls']:
            for table, name in (('kind', call['kind']), ('site', '%s @ %s' % (call['site'], call['stage']))):
                row = tables[table][name]
                row['cpu'] += call['cpu'] or 0
                row['rss_growth_kib'] += max(call['rss_growth_kib'] or 0, 0)
                row['calls'] += 1
                row['failed'] += call['ok'] is False
                row['blocks'].add(entry['key'])
    return {table: sorted(({'name': name, **dict(value, blocks=len(value['blocks']), cpu=round(value['cpu'], 1))}
                           for name, value in rows.items()), key=lambda row: -row['cpu'])
            for table, rows in tables.items()}


# ---------------------------------------------------------------- rendering

def number(value, digits=1):
    if value is None:
        return '-'
    if isinstance(value, float):
        return ('%.' + str(digits) + 'f') % value
    return str(value)


def giga(value):
    return '-' if value is None else '%.1f' % (value / 1e9)


def delta(new, old, percent=True):
    if new is None or old is None:
        return '-'
    if percent:
        return '%+.1f%%' % (100.0 * (new - old) / old) if old else '-'
    return '%+.2f' % (new - old)


def gib(kib):
    return '-' if kib is None else '%.2f' % (kib / 2**20)


def call_row(call):
    return '| %s | %s | %s | %s | %s | %s | %s | %s | %s |' % (
        call['kind'], call['stage'] or '-', call['site'] or '-', number(call['facts']), number(call['nodes']),
        number(call['goal']), number(call['cpu'], 2), {True: 'yes', False: 'no', None: '-'}[call['ok']],
        gib(call['rss_growth_kib']))


def leftover_classes(block):
    counts = defaultdict(int)
    for leftover in block['leftovers']:
        counts[leftover['class']] += 1
    if not counts and block['verdict'] != 'CLOSED':
        for error in block['errors']:
            first = next((line.strip() for line in error['text'].splitlines()
                          if line.strip() and line.strip() != 'Error:'), 'error')
            counts['(no export) ' + re.sub(r'^\(in proof [^)]*\):\s*', '', first)[:80]] += 1
    return dict(counts)


def render_block(entry, base_entry=None):
    member, block, row = entry['member'], entry['block'], entry['row']
    lines = ['### ' + member_name(member), '']
    if block is None:
        return lines + ['not run' + (' (%s)' % row.get('error') if row and row.get('error') else ''), '']
    old = base_entry['block'] if base_entry else None
    head = '| verdict | end | CPU s | instr (G) | peak GiB | wall s | stage reached |'
    lines += [head, '|---|---|---|---|---|---|---|',
              '| %s | %s | %s | %s | %s | %s | %s |' % (block['verdict'], block['end'], number(block['cpu']),
                                                         giga(block['instructions']), number(block['peak_gib'], 2),
                                                         number(block['wall']), block['stage'])]
    if old is not None:
        lines.append('| base: %s | %s | %s (%s) | %s (%s) | %s (%s) | %s | %s |' % (
            old['verdict'], old['end'], number(old['cpu']), delta(block['cpu'], old['cpu']),
            giga(old['instructions']), delta(block['instructions'], old['instructions']),
            number(old['peak_gib'], 2), delta(block['peak_gib'], old['peak_gib'], percent=False),
            number(old['wall']), old['stage']))
    if block['reason'] and block['verdict'] != 'CLOSED':
        lines += ['', 'reason: ' + block['reason']]
    lines += ['', 'stages: ' + (', '.join('%s %s s/%s' % (name, number(stage['cpu']), stage['steps'])
                                          for name, stage in sorted(block['stages'].items(),
                                                                    key=lambda item: -(item[1]['cpu'] or 0)))
                                or '-')]
    calls = block['calls']
    lines += ['', 'solver calls: %d (telemetry lines %d, export records %d, samples %d)' % (
        len(calls), block['telemetry_events'], block['exports'], block['samples'])]
    header = ['| kind | stage | site | facts | nodes | goal | CPU s | ok | RSS +GiB |', '|---|---|---|---|---|---|---|---|---|']
    if calls:
        lines += ['', 'top 5 by time:', ''] + header
        lines += [call_row(call) for call in sorted(calls, key=lambda call: -(call['cpu'] or 0))[:5]]
        grown = [call for call in calls if call['rss_growth_kib']]
        if grown:
            lines += ['', 'top 5 by RSS growth:', ''] + header
            lines += [call_row(call) for call in sorted(grown, key=lambda call: -call['rss_growth_kib'])[:5]]
    classes = leftover_classes(block)
    lines += ['', 'leftover goal classes: ' + (', '.join('%s x%d' % item for item in sorted(classes.items())) or '-'), '']
    return lines


def render_ranking(rank, limit=10):
    lines = ['## Ranking across the set', '',
             'Telemetry stages include their nested stages, and a solver call includes the calls it wraps '
             '(Lia.lia over xlia and zify): compare rows of one level, do not add them up.', '']
    for table, title, extra in (('stage', 'stage', 'steps'), ('kind', 'solver kind', 'calls'),
                                ('site', 'site @ stage', 'calls')):
        rows = rank[table]
        lines += ['by %s (CPU s, RSS growth GiB, blocks, %s%s):' % (title, extra, ', failed' if extra == 'calls' else ''), '']
        if not rows:
            lines += ['-', '']
            continue
        lines += ['| %s | CPU s | RSS +GiB | blocks | %s |%s' % (title, extra, ' failed |' if extra == 'calls' else ''),
                  '|---|---|---|---|---|' + ('---|' if extra == 'calls' else '')]
        for row in rows[:limit]:
            lines.append('| %s | %s | %s | %d | %d |%s' % (row['name'], number(row['cpu']), gib(row['rss_growth_kib']),
                                                         row['blocks'], row[extra],
                                                         ' %d |' % row['failed'] if extra == 'calls' else ''))
        by_memory = sorted(rows, key=lambda row: -row['rss_growth_kib'])[:3]
        if any(row['rss_growth_kib'] for row in by_memory):
            lines += ['', 'most memory: ' + ', '.join('%s %s GiB' % (row['name'], gib(row['rss_growth_kib']))
                                                     for row in by_memory if row['rss_growth_kib'])]
        lines.append('')
    return lines


def summary(run):
    blocks = [entry['block'] for entry in run['blocks'] if entry['block']]
    return {'members': len(run['blocks']), 'ran': len(blocks),
            'closed': sum(block['verdict'] == 'CLOSED' for block in blocks),
            'cpu': round(sum(block['cpu'] or 0 for block in blocks), 1),
            'instructions': sum(block['instructions'] or 0 for block in blocks),
            'peak_gib': max((block['peak_gib'] or 0 for block in blocks), default=None)}


def render(run, base=None):
    meta = run['meta']
    total = summary(run)
    lines = ['# %s run %s' % (meta['set'], Path(run['dir']).name), '',
             'head %s, rules %s, bench head %s, bank %s, telemetry %s' % (
                 meta['head'][:12], (meta.get('rules') or meta['head'])[:12], (meta.get('bench_head') or '-')[:12],
                 meta.get('bank', '-'), 'on' if meta.get('telemetry') else 'off'), '',
             'closed %d of %d (ran %d); CPU %s s; instructions %s G; max peak %s GiB' % (
                 total['closed'], total['members'], total['ran'], number(total['cpu']), giga(total['instructions']),
                 number(total['peak_gib'], 2))]
    base_blocks = {}
    if base is not None:
        old = summary(base)
        base_blocks = {entry['key']: entry for entry in base['blocks']}
        lines.append('base %s: closed %d; CPU %s s (%s); instructions %s G (%s); max peak %s GiB' % (
            Path(base['dir']).name, old['closed'], number(old['cpu']), delta(total['cpu'], old['cpu']),
            giga(old['instructions']), delta(total['instructions'], old['instructions']), number(old['peak_gib'], 2)))
        changed = [entry['key'] for entry in run['blocks'] if entry['block'] and entry['key'] in base_blocks
                   and base_blocks[entry['key']]['block']
                   and entry['block']['verdict'] != base_blocks[entry['key']]['block']['verdict']]
        lines.append('verdict changes: ' + (', '.join(changed) or 'none'))
    lines.append('')
    for entry in run['blocks']:
        lines += render_block(entry, base_blocks.get(entry['key']))
    lines += render_ranking(ranking(run))
    return '\n'.join(lines) + '\n'


def report_json(run):
    """The machine-readable report: per block figures (calls trimmed to the top 20) and the ranking."""
    blocks = []
    for entry in run['blocks']:
        block = entry['block']
        if block is not None:
            calls = sorted(block['calls'], key=lambda call: -(call['seconds'] or 0))[:20]
            block = dict(block, calls=[{key: value for key, value in call.items() if key != 'fields'} for call in calls],
                         leftovers=leftover_classes(block), errors=[error['text'][:400] for error in block['errors']])
        blocks.append({'key': entry['key'], 'member': entry['member'], 'block': block})
    return {'meta': run['meta'], 'summary': summary(run), 'blocks': blocks, 'ranking': ranking(run)}
