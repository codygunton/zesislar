#!/usr/bin/env python3
"""The obligation store: one append-only event log per function (plan A2). It calls no model.

    store.py add    --run RUN EVENT_JSON        append one event (or '-' for one JSON row per stdin line)
    store.py status --run RUN [--counts]        fold the log into the current state
    store.py sync   --function F --run RUN [--callers FILE]
                                                derive states from the existing evidence

RUN is the function's run directory (default `_build/agents/aa/<function>/` with --function).
The log is RUN/OBLIGATIONS.jsonl; every append holds an exclusive `flock` on it.

Event row, schema `oblig-event/1`: id, function, kind (block, goal, meaning, decision), parent,
state, class, tier, attempt, prompt_sha256, prompt_bytes, answer_bytes, tokens_in, tokens_out,
context_items, context_used, artifact {path, sha256}, head. The fold keeps the last state of each id.
States: derived, running, closed, failed (with class), false, waiting-decision, blocked-on (the
blocking id is the event's class). A prover attempt is an event whose `attempt` is set; the store
rejects an attempt whose (prompt_sha256, tier) pair already exists for that id. An event `derived`
on an id that was in another state is a reset (a changed input).

Ids: <function>/block/<case>, <function>/goal/<case>-<16 hex of the statement sha256>,
<function>/decision/<kind>-<offset>, <function>/meaning/<lemma name>; <case> and <offset> are 4-hex
offsets from the function's symbol (a caller case may carry its slot suffix).

sync adds no second source of truth: it reads CALLERS.json rows (tools/block/render_function_callers.py),
CLOSURE.json / NOT-CLOSED.json (tools/closure_cert.py) in the run directory, in the bench result
dirs and in tools/block/closures/<callers>/<case>/, results.jsonl (tools/bench/bench.py) and
goals/<id>/STATUS.json of residual runs under RUN (tools/block/residual_loop.py), and appends an
event only where the derived state differs from the folded one. A CLOSURE.json counts only when its
caller_sha256 equals the caller of the current CALLERS.json row. It files each open request of
RUN/round-<n>/derived/REQUESTS.json (derive.py, schema oblig-requests/1; latest round wins, `answered`
ones left out) as a `decision` obligation under the request's id, state `derived`; a request with a
`proposal` carries it as the artifact {path of that REQUESTS.json, sha256 of the proposal's canonical
JSON}, filed again only when the id never carried that proposal.

status --counts prints one line per kind and state, then the totals; the coordinator reads only this
and `route.py next`, and both record the bytes they print to RUN/COORDINATOR.jsonl.
"""
import argparse
import fcntl
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[2]
SCHEMA = 'oblig-event/1'
LOG = 'OBLIGATIONS.jsonl'
COORDINATOR = 'COORDINATOR.jsonl'
FIELDS = ('id', 'function', 'kind', 'parent', 'state', 'class', 'tier', 'attempt', 'prompt_sha256',
          'prompt_bytes', 'answer_bytes', 'tokens_in', 'tokens_out', 'context_items', 'context_used',
          'artifact', 'head')
KINDS = ('block', 'goal', 'meaning', 'decision')
STATES = ('derived', 'running', 'closed', 'failed', 'false', 'waiting-decision', 'blocked-on')
DECISION_KINDS = ('contract', 'callee_premise', 'loop_assertion', 'join_assertion', 'access_placement',
                  'call_row', 'predicate')
CASE = r'[0-9a-f]{4}[0-9a-z_]*'
ID_FORMS = {
    'block': re.compile(r'^(?P<function>[^/\s]+)/block/(?P<case>%s)$' % CASE),
    'goal': re.compile(r'^(?P<function>[^/\s]+)/goal/(?P<case>%s)-(?P<statement>[0-9a-f]{16})$' % CASE),
    'decision': re.compile(r'^(?P<function>[^/\s]+)/decision/(?P<decision>%s)-(?P<offset>[0-9a-f]{4})$'
                           % '|'.join(DECISION_KINDS)),
    'meaning': re.compile(r"^(?P<function>[^/\s]+)/meaning/(?P<lemma>[A-Za-z_][\w']*)$"),
}


class Rejected(Exception):
    """The store refuses the event; the message is the reason."""


def sha256_bytes(data):
    return hashlib.sha256(data).hexdigest()


def sha256_file(path):
    return sha256_bytes(Path(path).read_bytes())


def block_id(function, case):
    return '%s/block/%s' % (function, case)


def goal_id(function, case, statement):
    return '%s/goal/%s-%s' % (function, case, sha256_bytes(statement.encode())[:16])


def decision_id(function, kind, offset):
    return '%s/decision/%s-%s' % (function, kind, offset)


def meaning_id(function, lemma):
    return '%s/meaning/%s' % (function, lemma)


def parse_id(identifier):
    """(kind, match groups) of an obligation id, or None."""
    for kind, form in ID_FORMS.items():
        match = form.match(identifier or '')
        if match:
            return kind, match.groupdict()
    return None


def default_run(function):
    return ROOT / '_build' / 'agents' / 'aa' / function


def git_head():
    result = subprocess.run(['git', '-C', str(ROOT), 'rev-parse', 'HEAD'], capture_output=True, text=True)
    return result.stdout.strip() or None


def event(**fields):
    """A complete event row: every schema field, unknown fields refused."""
    unknown = set(fields) - set(FIELDS)
    if unknown:
        raise Rejected('unknown event fields: ' + ', '.join(sorted(unknown)))
    row = {'schema': SCHEMA}
    row.update({name: fields.get(name) for name in FIELDS})
    return row


def validate(row):
    if row.get('schema') != SCHEMA:
        raise Rejected('schema is not %s' % SCHEMA)
    parsed = parse_id(row.get('id'))
    if parsed is None:
        raise Rejected('malformed id: %r' % row.get('id'))
    kind, groups = parsed
    if row.get('kind') != kind:
        raise Rejected('id %s is of kind %s, event says %r' % (row['id'], kind, row.get('kind')))
    if row.get('function') != groups['function']:
        raise Rejected('id %s names another function than %r' % (row['id'], row.get('function')))
    if row.get('state') not in STATES:
        raise Rejected('unknown state %r' % row.get('state'))
    if row['state'] in ('failed', 'blocked-on') and not row.get('class'):
        raise Rejected('state %s needs a class (failure class or blocking id)' % row['state'])
    if row['state'] == 'blocked-on' and parse_id(row['class']) is None:
        raise Rejected('blocked-on names no obligation id: %r' % row['class'])
    if row.get('attempt') is not None and (not row.get('prompt_sha256') or not row.get('tier')):
        raise Rejected('an attempt event needs prompt_sha256 and tier')
    artifact = row.get('artifact')
    if artifact is not None and not (isinstance(artifact, dict) and set(artifact) == {'path', 'sha256'}):
        raise Rejected('artifact must be {path, sha256}')


def read_events(run):
    path = Path(run) / LOG
    if not path.exists():
        return []
    return [json.loads(line) for line in path.read_text().splitlines() if line.strip()]


def append(run, rows):
    """Append validated rows under flock; reject a repeated (prompt_sha256, tier) of an id."""
    rows = [rows] if isinstance(rows, dict) else list(rows)
    for row in rows:
        validate(row)
    Path(run).mkdir(parents=True, exist_ok=True)
    with open(Path(run) / LOG, 'a+') as handle:
        fcntl.flock(handle, fcntl.LOCK_EX)
        handle.seek(0)
        seen = set()
        for line in handle.read().splitlines():
            if line.strip():
                old = json.loads(line)
                if old.get('attempt') is not None:
                    seen.add((old['id'], old.get('prompt_sha256'), old.get('tier')))
        fresh = []
        for row in rows:
            if row.get('attempt') is not None:
                key = (row['id'], row['prompt_sha256'], row['tier'])
                # The running and the result event of one attempt share the pair.
                same_attempt = any(r['id'] == row['id'] and r.get('attempt') == row['attempt']
                                   and r.get('tier') == row['tier'] for r in fresh)
                if key in seen and not same_attempt and not continues(handle, row):
                    raise Rejected('prompt %s already sent to tier %s for %s'
                                   % (row['prompt_sha256'][:16], row['tier'], row['id']))
                seen.add(key)
            fresh.append(row)
        handle.seek(0, os.SEEK_END)
        for row in fresh:
            handle.write(json.dumps(row, sort_keys=True) + '\n')
        handle.flush()
    return rows


def continues(handle, row):
    """True when ROW belongs to an attempt still open in the log: the last event of this id, tier and
    attempt number is its `running` event with the same prompt. The result event of an attempt, and the
    running event a best-of-N round (tools/oblig/drive.py settle_round) announces again for the sample it
    submits after its sibling samples' results, are events of an attempt already sent, not a new send."""
    handle.seek(0)
    last = None
    for line in handle.read().splitlines():
        if line.strip():
            old = json.loads(line)
            if (old['id'] == row['id'] and old.get('attempt') == row['attempt']
                    and old.get('tier') == row['tier']):
                last = old
    return last is not None and last['state'] == 'running' and last['prompt_sha256'] == row['prompt_sha256']


def fold(events):
    """The current state of every id, in order of first appearance."""
    state = {}
    for row in events:
        item = state.get(row['id'])
        if item is None:
            item = state[row['id']] = dict(
                id=row['id'], function=row['function'], kind=row['kind'], parent=None, state=None,
                goal_class=None, failure=None, blocked_by=None, tier=None, artifact=None, closed_by=None,
                attempts=[], tier_attempts={}, last_attempt=None, resets=0, events=[])
        if item['state'] not in (None, 'derived') and row['state'] == 'derived':
            item['resets'] += 1
        item['events'].append(row)
        item['state'] = row['state']
        if row.get('parent'):
            item['parent'] = row['parent']
        if row.get('tier'):
            item['tier'] = row['tier']
        if row.get('artifact'):
            item['artifact'] = row['artifact']
        if row['state'] == 'failed':
            item['failure'] = row['class']
        elif row['state'] == 'blocked-on':
            item['blocked_by'] = row['class']
        elif row.get('class'):
            item['goal_class'] = row['class']
        if row['state'] == 'closed':
            item['closed_by'] = row.get('tier')
        if row.get('attempt') is not None:
            key = (row['tier'], row['attempt'])
            if key not in [(a['tier'], a['attempt']) for a in item['attempts']]:
                item['attempts'].append(dict(tier=row['tier'], attempt=row['attempt']))
                item['tier_attempts'][row['tier']] = item['tier_attempts'].get(row['tier'], 0) + 1
            item['last_attempt'] = dict(tier=row['tier'], attempt=row['attempt'], state=row['state'],
                                        failure=row['class'] if row['state'] == 'failed' else None)
    return state


def is_open(item):
    return item['state'] != 'closed'


def round_number(run):
    numbers = [int(m.group(1)) for p in Path(run).glob('round-*')
               for m in [re.fullmatch(r'round-(\d+)', p.name)] if m and p.is_dir()]
    return max(numbers, default=0)


def record_coordinator_read(run, tool, text):
    """Log the bytes a coordinator-facing command printed, by round (report.py sums them)."""
    run = Path(run)
    if not run.is_dir():
        return
    row = {'round': round_number(run), 'tool': tool, 'bytes': len(text.encode())}
    with open(run / COORDINATOR, 'a') as handle:
        fcntl.flock(handle, fcntl.LOCK_EX)
        handle.write(json.dumps(row, sort_keys=True) + '\n')


def count_lines(state):
    counts = {}
    for item in state.values():
        counts[(item['kind'], item['state'])] = counts.get((item['kind'], item['state']), 0) + 1
    lines = ['%s %s %d' % (kind, st, n) for (kind, st), n in
             sorted(counts.items(), key=lambda kv: (KINDS.index(kv[0][0]), STATES.index(kv[0][1])))]
    lines.append('total %d open %d' % (len(state), sum(is_open(item) for item in state.values())))
    return lines


def status_lines(state):
    lines = []
    for item in state.values():
        extra = item['failure'] if item['state'] == 'failed' else (
            item['blocked_by'] if item['state'] == 'blocked-on' else item['goal_class'])
        lines.append('%s %s %s attempts=%d resets=%d tier=%s' % (
            item['id'], item['state'], extra or '-', len(item['attempts']), item['resets'], item['tier'] or '-'))
    return lines


# --- sync -------------------------------------------------------------------------------------

def read_json(path, default=None):
    try:
        return json.loads(Path(path).read_text())
    except (OSError, ValueError):
        return default


def artifact_of(path):
    return {'path': str(path), 'sha256': sha256_file(path)}


def find_callers(function, run, explicit=None):
    candidates = [Path(explicit)] if explicit else [Path(run) / 'callers' / 'CALLERS.json',
                                                     Path(run) / 'CALLERS.json']
    for path in candidates:
        data = read_json(path)
        if data and data.get('function') == function:
            return path, data
    if explicit:
        raise SystemExit('no CALLERS.json of %s at %s' % (function, explicit))
    for path in sorted((ROOT / 'tools' / 'block' / 'generated').glob('*/CALLERS.json')):
        data = read_json(path)
        if data and data.get('function') == function:
            return path, data
    return None, None


def bench_rows(function, run):
    rows = []
    run = Path(run)
    for path in [run / 'results.jsonl', *sorted(run.glob('*/results.jsonl')), *sorted(run.glob('*/*/results.jsonl'))]:
        if path.is_file():
            for line in path.read_text().splitlines():
                if line.strip():
                    row = json.loads(line)
                    if row.get('function') == function:
                        rows.append(row)
    return rows


def block_evidence(case, row, run, callers_name, results):
    """(state, class, artifact path) of one block from its closure records and bench rows."""
    want = (row.get('caller') or {}).get('sha256')
    directories = [Path(run) / 'runs' / case, Path(run) / case, Path(run) / 'closures' / case]
    directories += [Path(r['dir']) for r in results if r.get('case') == case and r.get('dir')]
    if callers_name:
        directories.append(ROOT / 'tools' / 'block' / 'closures' / callers_name / case)
    stale = failed = None
    for directory in directories:
        closure = read_json(directory / 'CLOSURE.json')
        if closure and closure.get('verdict') == 'CLOSED':
            if want is None or closure.get('caller_sha256') == want:
                return 'closed', None, directory / 'CLOSURE.json'
            stale = directory / 'CLOSURE.json'
        refusal = read_json(directory / 'NOT-CLOSED.json')
        if refusal and failed is None and (want is None or refusal.get('caller_sha256') in (None, want)):
            failed = directory / 'NOT-CLOSED.json'
    if failed is not None:
        return 'failed', 'not_closed', failed
    if any(r.get('case') == case and r.get('verdict') not in (None, 'CLOSED') for r in results):
        return 'failed', 'not_closed', None
    return 'derived', 'stale_closure' if stale else None, None


def residual_runs(run, depth=3):
    """Directories under RUN that hold a residual_loop.py run (MANIFEST.json and goals/)."""
    found = []
    base = len(Path(run).parts)
    for directory, subdirs, files in os.walk(run):
        here = Path(directory)
        if 'MANIFEST.json' in files and (here / 'goals').is_dir():
            found.append(here)
        if len(here.parts) - base >= depth:
            subdirs[:] = []
        subdirs[:] = [d for d in subdirs if d not in ('goals', '_findlib', 'leftover')]
    return sorted(found)


GOAL_RESULTS = {'PASS': ('closed', None), 'FAIL': ('failed', 'compile_error'),
                'REFUSED': ('failed', 'reparse'), 'OPEN': ('derived', None)}


def derived_states(function, run, callers=None):
    """{id: (kind, parent, state, class, artifact path)} from the evidence."""
    out = {}
    path, data = find_callers(function, run, callers)
    results = bench_rows(function, run)
    if data:
        callers_name = path.parent.name
        for row in data.get('rows', []):
            case = row['case']
            if row.get('status') == 'inlined':
                continue
            if row.get('status') == 'refused':
                out[block_id(function, case)] = ('block', None, 'failed', 'REFUSED', path)
                continue
            st, cls, artifact = block_evidence(case, row, run, callers_name, results)
            out[block_id(function, case)] = ('block', None, st, cls, artifact)
    for directory in residual_runs(run):
        manifest = read_json(directory / 'MANIFEST.json', {})
        case = manifest.get('block')
        for goal in manifest.get('goals', []):
            statement = goal.get('statement')
            if not case or not statement:
                continue
            gdir = directory / 'goals' / goal['id']
            status = read_json(gdir / 'STATUS.json', {})
            st, cls = GOAL_RESULTS.get(status.get('result', 'OPEN'), ('derived', None))
            proof = gdir / 'proof.v'
            artifact = proof if st == 'closed' and proof.is_file() else (gdir / 'STATUS.json'
                                                                         if status else None)
            out[goal_id(function, case, statement)] = ('goal', block_id(function, case), st, cls, artifact)
    return out


def round_requests(function, run):
    """{decision id: (request row, REQUESTS.json path)} over RUN/round-<n>/derived/REQUESTS.json
    (schema oblig-requests/1 of derive.py), the latest round winning; answered requests are left out."""
    rounds = sorted((int(m.group(1)), p) for p in Path(run).glob('round-*')
                    for m in [re.fullmatch(r'round-(\d+)', p.name)] if m)
    found = {}
    for _, directory in rounds:
        path = directory / 'derived' / 'REQUESTS.json'
        data = read_json(path)
        if not isinstance(data, dict):
            continue
        answered = set(data.get('answered') or [])
        for row in data.get('requests') or []:
            identifier = row.get('id') or decision_id(function, row.get('kind'),
                                                      '%04x' % int(str(row.get('pc')).lstrip('+'), 16))
            parsed = parse_id(identifier)
            if (parsed is None or parsed[0] != 'decision' or parsed[1]['function'] != function
                    or parsed[1]['decision'] != row.get('kind')):
                raise Rejected('request %r of %s is no decision id of kind %r' % (identifier, path, row.get('kind')))
            if identifier in answered:
                found.pop(identifier, None)
            else:
                found[identifier] = (row, path)
        for identifier in answered:
            found.pop(identifier, None)
    return found


def proposal_artifact(row, path):
    """A request's proposal as a decision artifact: the REQUESTS.json that holds the row (find it by
    the obligation id) and the sha256 of the proposal's canonical JSON."""
    if row.get('proposal') is None:
        return None
    text = json.dumps(row['proposal'], sort_keys=True, separators=(',', ':'))
    return {'path': str(path), 'sha256': sha256_bytes(text.encode())}


def sync(function, run, callers=None):
    """Append the events that bring the store to the evidence; return the number appended."""
    state = fold(read_events(run))
    head = git_head()
    rows = []
    for identifier, (kind, parent, st, cls, artifact) in derived_states(function, run, callers).items():
        item = state.get(identifier)
        current = item['state'] if item else None
        if st == 'closed':
            write = current != 'closed'
        elif st == 'failed':
            write = current in (None, 'derived', 'running', 'closed') and not (
                current == 'failed' and item['failure'] == cls)
        else:
            write = current in (None, 'closed')
        if write:
            rows.append(event(id=identifier, function=function, kind=kind, parent=parent, state=st,
                              **{'class': cls}, tier='evidence' if st == 'closed' else None,
                              artifact=artifact_of(artifact) if artifact else None, head=head))
    # Each open request is a decision obligation. A request proposal the id has never carried
    # (re)derives it with the proposal as its artifact, so the router checks it with no model; a
    # proposal filed later by an agent is never replaced by an older derived one.
    for identifier, (row, path) in round_requests(function, run).items():
        item = state.get(identifier)
        artifact = proposal_artifact(row, path)
        carried = {(e.get('artifact') or {}).get('sha256') for e in item['events']} if item else set()
        if item is None or (artifact and item['state'] != 'closed' and artifact['sha256'] not in carried):
            rows.append(event(id=identifier, function=function, kind='decision', state='derived',
                              artifact=artifact, head=head))
    if rows:
        append(run, rows)
    return len(rows)


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__.split('\n')[0])
    commands = parser.add_subparsers(dest='command', required=True)
    for name in ('add', 'status', 'sync'):
        command = commands.add_parser(name)
        command.add_argument('--function')
        command.add_argument('--run', type=Path)
        if name == 'add':
            command.add_argument('event', help="one event as JSON, or '-' for JSON lines on stdin")
        if name == 'status':
            command.add_argument('--counts', action='store_true')
        if name == 'sync':
            command.add_argument('--callers', type=Path, help='CALLERS.json to use instead of the search')
    options = parser.parse_args(argv)
    if options.run is None:
        if not options.function:
            parser.error('--run or --function is required')
        options.run = default_run(options.function)
    try:
        if options.command == 'add':
            text = sys.stdin.read() if options.event == '-' else options.event
            rows = [json.loads(line) for line in text.splitlines() if line.strip()]
            append(options.run, [event(**{k: v for k, v in r.items() if k != 'schema'}) for r in rows])
            print('added %d' % len(rows))
        elif options.command == 'status':
            state = fold(read_events(options.run))
            if options.function:
                state = {k: v for k, v in state.items() if v['function'] == options.function}
            text = '\n'.join(count_lines(state) if options.counts else status_lines(state)) + '\n'
            sys.stdout.write(text)
            if options.counts:
                record_coordinator_read(options.run, 'store.status', text)
        else:
            if not options.function:
                parser.error('sync needs --function')
            added = sync(options.function, options.run, options.callers)
            state = fold(read_events(options.run))
            blocks = [i for i in state.values() if i['kind'] == 'block']
            print('sync %s: %d events added' % (options.function, added))
            for line in count_lines(state):
                print(line)
            print('blocks closed %d of %d; open obligations %d' % (
                sum(i['state'] == 'closed' for i in blocks), len(blocks), sum(is_open(i) for i in state.values())))
    except Rejected as error:
        print('rejected: %s' % error, file=sys.stderr)
        return 1
    return 0


if __name__ == '__main__':
    sys.exit(main())
