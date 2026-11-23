#!/usr/bin/env python3
"""The obligation report of one function (plan A7). It calls no model.

    report.py --function F [--run RUN]

Prints one line per measure, `n/a` where its input is absent: blocks closed with no model; rounds
and requests per round (RUN/round-<n>/derived/REQUESTS.json, schema oblig-requests/1 of derive.py);
decisions made against the floor (round 1's contract, loop_assertion and callee_premise requests,
answered ones included); share of requests with `derivable` true; unhandled refusals per round
(`refusals_without_request`); proposals rejected by
machine runs; missing-context failures per attempt; share of supplied context items absent from the
accepted proof (context_items/context_used of the closing attempts) and of premises dropped by the
premise minimiser of residual_loop.py; goals found false after a model attempt; prompt bytes and
tokens per attempt; coordinator bytes read per round (RUN/COORDINATOR.jsonl); per tier the share
closed at the first attempt and within its attempts; per tier the check_proof calls per goal it closed
and the tokens per attempt with and without the tool (`check_calls:<n>` in an attempt's context_items);
share closed by Haiku tiers; goals that reached opus-medium as prover; escalations; tokens per closed
obligation per tier; spin count; tokens and checked-lemma lines per block.
"""
import argparse
import json
from pathlib import Path
import re
import sys

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import route  # noqa: E402
import store  # noqa: E402

NO_MODEL_TIERS = {'mechanical', 'evidence', 'falsify', 'machine-run', 'kernel', 'derived', None}
FLOOR_KINDS = ('contract', 'loop_assertion', 'callee_premise')


def ratio(numerator, denominator, percent=True):
    if not denominator:
        return 'n/a'
    return '%.1f%%' % (100.0 * numerator / denominator) if percent else '%.1f' % (numerator / denominator)


def rounds(run):
    """{round number: REQUESTS.json of that round (schema oblig-requests/1) or an empty one}."""
    found = {}
    for directory in Path(run).glob('round-*'):
        match = re.fullmatch(r'round-(\d+)', directory.name)
        if not match:
            continue
        data = {}
        for path in (directory / 'derived' / 'REQUESTS.json', directory / 'REQUESTS.json'):
            data = store.read_json(path)
            if data is not None:
                break
        data = data if isinstance(data, dict) else {'requests': data or []}
        found[int(match.group(1))] = dict(requests=data.get('requests') or [], answered=data.get('answered') or [],
                                          refusals=data.get('refusals_without_request') or [])
    return dict(sorted(found.items()))


def request_kind(identifier):
    parsed = store.parse_id(identifier)
    return parsed[1].get('decision') if parsed else None


def attempt_rows(item):
    """The result event of each attempt (last event carrying that tier and attempt number)."""
    last = {}
    for row in item['events']:
        if row.get('attempt') is not None:
            last[(row['tier'], row['attempt'])] = row
    return list(last.values())


def model_tier(tier):
    return tier not in NO_MODEL_TIERS


def counted(value, prefix=None):
    """A count field: an int as is; a list (drive.py's context_items) by its entries, only those starting
    with PREFIX when given."""
    if isinstance(value, list):
        return sum(1 for entry in value if prefix is None or str(entry).startswith(prefix))
    return value or 0


def check_calls(row):
    """The check_proof calls of an attempt result row (`check_calls:<n>` in context_items), None without
    the tool."""
    items = row.get('context_items')
    for entry in items if isinstance(items, list) else []:
        if str(entry).startswith('check_calls:'):
            return int(str(entry).split(':', 1)[1])
    return None


def tokens(row):
    return (row.get('tokens_in') or 0) + (row.get('tokens_out') or 0)


def measures(run, function=None):
    state = {k: v for k, v in store.fold(store.read_events(run)).items()
             if function is None or v['function'] == function}
    items = list(state.values())
    blocks = [i for i in items if i['kind'] == 'block']
    goals = [i for i in items if i['kind'] in ('goal', 'meaning')]
    decisions = [i for i in items if i['kind'] == 'decision']
    attempts = [row for i in items for row in attempt_rows(i)]
    out = []

    def put(name, value):
        out.append((name, value))

    def descendants(identifier):
        found = [i for i in items if i['parent'] == identifier]
        return found + [d for i in found for d in descendants(i['id'])]

    closed_blocks = [b for b in blocks if b['state'] == 'closed']
    no_model = [b for b in closed_blocks if not any(model_tier(a['tier'])
                                                     for d in descendants(b['id']) for a in d['attempts'])]
    put('blocks closed with no model', '%d of %d closed (%d blocks)' % (len(no_model), len(closed_blocks), len(blocks))
        if blocks else 'n/a')

    by_round = rounds(run)
    put('rounds', str(len(by_round)) if by_round else 'n/a')
    put('requests per round', ' '.join('%d:%d' % (n, len(r['requests'])) for n, r in by_round.items()) or 'n/a')
    requests = [row for r in by_round.values() for row in r['requests']]
    first = by_round.get(1)
    # Round 1 issues every floor request; one already answered by an annotation is listed in `answered`.
    floor = (sum(row.get('kind') in FLOOR_KINDS for row in first['requests'])
             + sum(request_kind(i) in FLOOR_KINDS for i in first['answered'])) if first else None
    made = sum(d['state'] == 'closed' for d in decisions)
    put('decisions made / floor', 'n/a' if floor is None and not decisions else '%d / %s%s' % (
        made, floor if floor is not None else 'n/a', ' (%s x floor)' % ratio(made, floor, percent=False) if floor else ''))
    put('requests derivable', ratio(sum(bool(row.get('derivable')) for row in requests), len(requests)))
    put('unhandled refusals', ' '.join('%d:%d' % (n, len(r['refusals'])) for n, r in by_round.items())
        if by_round else 'n/a')
    tests = [row for i in items for row in i['events'] if row.get('tier') == 'machine-run']
    rejected = [row for row in tests if row['state'] == 'failed']
    put('proposals rejected by machine runs', '%d of %d tested' % (len(rejected), len(tests)) if tests else 'n/a')
    missing = sum(row['state'] == 'failed' and row.get('class') == 'need_context' for row in attempts)
    put('missing-context failures per attempt', '%d / %d (%s)' % (missing, len(attempts), ratio(missing, len(attempts)))
        if attempts else 'n/a')

    accepted = [row for row in attempts if row['state'] == 'closed' and row.get('context_items') is not None]
    supplied = sum(counted(row['context_items'], 'context:') for row in accepted)
    used = sum(counted(row.get('context_used')) for row in accepted)
    put('supplied context absent from accepted proof', ratio(supplied - used, supplied))
    before = after = 0
    for directory in store.residual_runs(run):
        for gdir in (directory / 'goals').iterdir():
            minimized = (store.read_json(gdir / 'STATUS.json', {}) or {}).get('minimized') or {}
            if minimized.get('state') == 'kept':
                before += minimized.get('binders_before', 0)
                after += minimized.get('binders_after', 0)
    put('premises dropped by the minimiser', ratio(before - after, before))

    def model_attempted_before_false(item):
        seen = False
        for row in item['events']:
            if row.get('attempt') is not None and model_tier(row['tier']):
                seen = True
            if row['state'] == 'false' and seen:
                return True
        return False
    put('goals found false after a model attempt', str(sum(model_attempted_before_false(g) for g in goals))
        if goals else 'n/a')

    prompt = [row['prompt_bytes'] for row in attempts if row.get('prompt_bytes') is not None]
    put('prompt bytes per attempt', ratio(sum(prompt), len(prompt), percent=False))
    put('answer bytes per attempt', ratio(sum(row.get('answer_bytes') or 0 for row in attempts
                                              if row.get('answer_bytes') is not None),
                                          sum(row.get('answer_bytes') is not None for row in attempts), percent=False))
    tokened = [row for row in attempts if row.get('tokens_in') is not None or row.get('tokens_out') is not None]
    put('tokens per attempt', ratio(sum((row.get('tokens_in') or 0) + (row.get('tokens_out') or 0) for row in tokened),
                                    len(tokened), percent=False))

    reads = {}
    path = Path(run) / store.COORDINATOR
    if path.is_file():
        for line in path.read_text().splitlines():
            if line.strip():
                row = json.loads(line)
                reads[row['round']] = reads.get(row['round'], 0) + row['bytes']
    put('coordinator bytes read per round', ' '.join('%d:%d' % kv for kv in sorted(reads.items())) or 'n/a')

    tiers = [name for name, _ in route.load_tiers()]
    for tier in tiers + sorted({a['tier'] for a in attempts if a['tier'] not in tiers}):
        reached = [g for g in goals if g['tier_attempts'].get(tier)]
        if not reached:
            put('tier %s' % tier, 'n/a')
            continue
        first = within = 0
        spent = 0
        for g in reached:
            rows = sorted((r for r in attempt_rows(g) if r['tier'] == tier), key=lambda r: r['attempt'])
            within += any(r['state'] == 'closed' for r in rows)
            first += bool(rows) and rows[0]['state'] == 'closed'
            spent += sum((r.get('tokens_in') or 0) + (r.get('tokens_out') or 0) for r in rows)
        closed_here = sum(g['closed_by'] == tier and g['state'] == 'closed' for g in reached)
        has_tokens = any(r.get('tokens_in') is not None or r.get('tokens_out') is not None
                         for g in reached for r in attempt_rows(g) if r['tier'] == tier)
        put('tier %s' % tier, 'reached %d, closed at first attempt %s, within its attempts %s, tokens per closed %s'
            % (len(reached), ratio(first, len(reached)), ratio(within, len(reached)),
               ratio(spent, closed_here, percent=False) if has_tokens else 'n/a'))
        tool_rows = [r for g in reached for r in attempt_rows(g) if r['tier'] == tier and check_calls(r) is not None]
        if tool_rows:
            plain = [r for g in reached for r in attempt_rows(g) if r['tier'] == tier and check_calls(r) is None
                     and r['state'] in ('closed', 'failed')]
            closed_by_tool = [g for g in reached if g['state'] == 'closed' and g['closed_by'] == tier]
            calls = sum(check_calls(r) for g in closed_by_tool for r in attempt_rows(g)
                        if r['tier'] == tier and check_calls(r) is not None)
            tokened_tool = [r for r in tool_rows if r.get('tokens_in') is not None or r.get('tokens_out') is not None]
            tokened_plain = [r for r in plain if r.get('tokens_in') is not None or r.get('tokens_out') is not None]
            put('check tool %s' % tier, 'attempts %d with the tool (%d without), check calls per closed goal %s, '
                'tokens per attempt with the tool %s, without %s'
                % (len(tool_rows), len(plain), ratio(calls, len(closed_by_tool), percent=False),
                   ratio(sum(map(tokens, tokened_tool)), len(tokened_tool), percent=False),
                   ratio(sum(map(tokens, tokened_plain)), len(tokened_plain), percent=False)))

    closed_goals = [g for g in goals if g['state'] == 'closed']
    put('pure goals closed by Haiku tiers', ratio(sum((g['closed_by'] or '').startswith('haiku') for g in closed_goals),
                                                  len(closed_goals)))
    put('goals that reached opus-medium as prover', ratio(sum(bool(g['tier_attempts'].get(route.TOP)) for g in goals),
                                                         len(goals)))
    escalations = sum(max(0, len({a['tier'] for a in g['attempts'] if model_tier(a['tier'])}) - 1) for g in goals)
    put('escalations', str(escalations) if goals else 'n/a')
    put('spin', str(sum(len(i['attempts']) >= route.SPIN_ATTEMPTS or i['resets'] >= route.SPIN_RESETS
                        for i in items)) if items else 'n/a')

    total_tokens = sum((r.get('tokens_in') or 0) + (r.get('tokens_out') or 0) for r in tokened)
    put('tokens per block', ratio(total_tokens, len(blocks), percent=False) if tokened else 'n/a')
    lines = None
    for g in closed_goals:
        artifact = g['artifact']
        if artifact and Path(artifact['path']).is_file() and Path(artifact['path']).suffix == '.v':
            lines = (lines or 0) + len(Path(artifact['path']).read_text(errors='replace').splitlines())
    put('checked-lemma lines per block', ratio(lines, len(blocks), percent=False) if lines is not None else 'n/a')
    return out


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__.split('\n')[0])
    parser.add_argument('--function', required=True)
    parser.add_argument('--run', type=Path)
    options = parser.parse_args(argv)
    run = options.run or store.default_run(options.function)
    for name, value in measures(run, options.function):
        print('%s: %s' % (name, value))
    return 0


if __name__ == '__main__':
    sys.exit(main())
