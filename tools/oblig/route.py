#!/usr/bin/env python3
"""The router: the next work items of one function's obligations (plan A7). It calls no model.

    route.py next --function F [--run RUN] [--limit N]

One line per item: `<id> <action> [tier=<tier>] <why>`, steps that need no model first, then prover
attempts cheapest tier first, then decision and diagnosis tasks, then the statement owner's queue,
then the obligations in spin. Actions:

  rerun      block `derived` (new, or reset by a changed annotation or lemma), or every leftover
             goal of a failed block closed: rerun the block (no model)
  derive     block refused by the render: derive.py turns the refusal into requests (no model)
  package    block not closed and no goal filed for it: package.py exports its leftovers (no model)
  falsify    pure goal not yet checked for falsity: falsify.py (no model)
  test       proposed contract or loop/join assertion: annotations.py test on the machine-run
             snapshots (no model)
  check      decision with a proposal (derived or tested): compile the annotations and rerun (no model)
  prove      pure goal: the tier named, on the class's ladder (see Ladder); a compiler error
             retries the same tier with the error text, `need_context` retries it with the named
             items, a malformed reply retries it once with a changed prompt; then the next tier
  diagnose   spatial leftover: diagnosis task at opus-medium
  decide     decision request without a proposal, or one whose proposal failed: opus-medium
  reconsider every prover tier failed (or the goal is `waiting-decision`): the assertion that
             produced the goal (its parent) is reconsidered at opus-medium
  owner      goal `false`, failure class `rule_gap`, or a goal naming a code address (ADDRESS):
             to the owner of the statement, with the counterexample
  spin       6 attempts or 3 resets (see Spin): reported, no further attempt until the statement changes

Ladder. A pure goal's ladder is `mechanical`, then the model tiers from the class's first tier on,
in tiers.json order, each with the attempts of the class's `attempts` row of routing.json (a class
row, else the row of its prefix before `-`, else routing.json's `default`; without any, the tier's
max_attempts). A tier with 0 attempts is not on the ladder. Only the attempts since the goal's
last reset (a `derived` event after another state: a changed statement, task or hint) count: a
reset runs the ladder again from its first tier, bounded by the 3-reset spin rule. Attempts a
tier spends:
- a proof attempt (`proved` that failed to compile, `give_up`, `need_context`, `false` refused)
  counts one;
- a `malformed` reply (no answer object) does not count as an attempt at the proof: the tier is
  retried once with a changed prompt; a second malformed reply at that tier counts;
- `need_context` is retried at the same tier only while the tier has attempts left; when the
  driver can supply none of the named items it files `failed` class `missing_context` (tier set,
  no attempt) and the goal goes to the next tier without spending that tier's next attempt;
- a tier whose prompt exceeds its bound (tiers.json, or the class's routing.json bound) is marked
  by the driver with `failed` class `too_large` (tier set, no attempt) and is skipped until the
  goal is reset; when every model tier of the ladder is marked, the driver files the goal
  `waiting-decision`, which this router sends to `reconsider`;
- a tier whose prompt the store refuses as sent before (an unchanged prompt after a reset, as the
  fixed `mechanical` one) is marked `failed` class `repeated_prompt` (no attempt) and skipped
  until the next reset.

Spin. The plan says "6 attempts in total"; its 5 tiers at 2 attempts each could never fit in that.
This router reads it as: an obligation on a ladder spins at 6 counted attempts (since its last
reset) or 3 resets only once its ladder is exhausted (the top ladder tier has had its attempts);
attempts at a tier that is not on the class's ladder (made before the ladder changed) do not
count toward the 6. Blocks,
decisions and spatial leftovers, which have no ladder, spin at 6 attempts or 3 resets as before.
An exhausted ladder below both limits gives `reconsider`.

Best-of-N. A tier may send N parallel samples per round (tools/oblig/drive.py: tiers.json or a class's
routing.json `samples`); each sample is an attempt of its own (its own prompt, registered running, its
own result event), and its running event names the round (`round:<first attempt of the round>` in
context_items). The ladder and spin rules read a round as ONE attempt: a tier's `attempts` in
routing.json count rounds, the 6-attempt spin limit counts rounds, and the round's result is the result
of the sample the driver submitted (its last result event; the others are `superseded`,
`compile_error`, `unconfirmed_false` or their own verdict). A retry after a compile error or
need_context is the next round.

Event vocabulary read here (written by the tools that act): tier `falsify` marks the falsity check
(state `false` on a hit, class `unchecked` when the binder types are outside its range); tier
`machine-run` marks `annotations.py test` (state `failed` class `rejected_by_run` on a rejection);
a decision's proposal is its event's artifact; failure classes of prover attempts are
`compile_error`, `need_context`, `give_up`, `rule_gap`, `malformed`, `bad_counterexample` (a `false`
whose counterexample the kernel did not confirm), `unconfirmed_false` (a `false` the attempt's
check_counterexample did not confirm, refused without a kernel call), `superseded` (a best-of-N
sample another sample of its round made unneeded), and `missing_context`, `too_large` and
`repeated_prompt` (filed by the driver, no attempt).

The tier order and default attempts come from tools/oblig/tiers.json, the first model tier and the
ladder attempts of a goal class from tools/oblig/routing.json; without them: mechanical,
haiku-low, haiku-medium, haiku-high, opus-medium, 2 attempts each (1 for the deterministic
`mechanical`), first model tier haiku-low.
"""
import argparse
import json
from pathlib import Path
import re
import sys

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import store  # noqa: E402

TIERS_FILE = HERE / 'tiers.json'
ROUTING_FILE = HERE / 'routing.json'
DEFAULT_TIERS = [('mechanical', 1), ('haiku-low', 2), ('haiku-medium', 2), ('haiku-high', 2), ('opus-medium', 2)]
DEFAULT_FIRST = 'haiku-low'
DEFAULT_CLASS = '*'
TOP = 'opus-medium'
SPIN_ATTEMPTS = 6
SPIN_RESETS = 3
# Leftover classes of tools/bench/triage_classes.json whose goal is an Iris entailment.
SPATIAL_CLASSES = {'SPATIAL', 'CALL', 'LOOKUP', 'EXIST', 'FAULT', 'HIST'}
ADDRESS = re.compile(r'0x800[0-9a-f]{5}|2148[0-9]{6}|21474[0-9]{5}')
TESTED_KINDS = ('contract', 'loop_assertion', 'join_assertion')
GROUPS = {'rerun': 0, 'derive': 0, 'package': 0, 'falsify': 0, 'test': 0, 'check': 0,
          'prove': 1, 'diagnose': 2, 'decide': 2, 'reconsider': 2, 'owner': 3, 'spin': 4}


def load_tiers(path=TIERS_FILE):
    """[(name, max_attempts)] cheapest first."""
    data = store.read_json(path)
    if data is None:
        return list(DEFAULT_TIERS)
    rows = data.get('tiers', data) if isinstance(data, dict) else data
    if isinstance(rows, dict):
        rows = [dict(name=name, **row) for name, row in rows.items()]
    return [(row['name'], int(row.get('max_attempts', 2))) for row in rows]


def load_routing(path=ROUTING_FILE):
    """The class rows of routing.json; its `default` row under the key DEFAULT_CLASS."""
    data = store.read_json(path) or {}
    if not isinstance(data, dict):
        return {}
    rows = dict(data.get('classes', data))
    if isinstance(data.get('default'), dict):
        rows[DEFAULT_CLASS] = data['default']
    return rows


def class_rows(routing, cls):
    """The routing rows that apply to CLS, most specific first."""
    keys = [cls, (cls or '').split('-')[0], DEFAULT_CLASS]
    return [routing[key] for key in keys if key and isinstance(routing.get(key), dict)]


def first_tier(routing, cls):
    for row in class_rows(routing, cls):
        if row.get('first_tier'):
            return row['first_tier']
    return DEFAULT_FIRST


def ladder(cls, tiers, routing):
    """[(tier, attempts)] of a goal class: mechanical, then the model tiers from its first tier."""
    order = [name for name, _ in tiers]
    limits = dict(tiers)
    attempts = next((row['attempts'] for row in class_rows(routing, cls) if isinstance(row.get('attempts'), dict)), {})
    model = [name for name in order if name != 'mechanical']
    start = first_tier(routing, cls)
    names = (['mechanical'] if 'mechanical' in order else []) + (model[model.index(start):] if start in model else model)
    return [(name, int(attempts.get(name, limits[name]))) for name in names if int(attempts.get(name, limits[name])) > 0]


def names_address(item):
    if item['goal_class'] == 'ADDRESS':
        return True
    artifact = item['artifact']
    if artifact and Path(artifact['path']).is_file():
        return bool(ADDRESS.search(Path(artifact['path']).read_text(errors='replace')))
    return False


def has_event(item, **match):
    return any(all(row.get(k) == v for k, v in match.items()) for row in item['events'])


def since_reset(item):
    """The events after the last reset to `derived`."""
    rows = item['events']
    last = max((i for i, row in enumerate(rows) if row['state'] == 'derived'
                and i > 0 and rows[i - 1]['state'] != 'derived'), default=0)
    return rows[last:]


def round_of(row):
    """The best-of-N round a running event names (`round:<first attempt>` in its context_items), or None."""
    for entry in row.get('context_items') or []:
        if str(entry).startswith('round:'):
            return int(str(entry).split(':', 1)[1])
    return None


def attempt_results(item):
    """{tier: [failure class or state of each ladder step, in order]} over the attempts since the goal's
    last reset (a reset, a changed task or statement, runs the ladder again). A ladder step is one
    attempt, or one best-of-N round (the samples whose running events name the same `round:<n>`): its
    result is the last result event of the round, the one of the sample the driver submitted."""
    final, rounds = {}, {}
    for row in since_reset(item):
        if row.get('attempt') is None:
            continue
        key = (row['tier'], row['attempt'])
        if round_of(row) is not None:
            rounds[key] = round_of(row)
        final[(row['tier'], rounds.get(key, row['attempt']))] = (
            row['class'] if row['state'] == 'failed' else row['state'])
    out = {}
    for (tier, _), result in final.items():
        out.setdefault(tier, []).append(result)
    return out


def spent(results):
    """Attempts a tier spent: every attempt but the first malformed reply."""
    malformed = results.count('malformed')
    return len(results) - malformed + max(0, malformed - 1)


def missing_context(item, tier):
    """True when the driver filed that it can supply none of the items TIER's last answer named."""
    last = item['events'][-1]
    return item['state'] == 'failed' and item['failure'] == 'missing_context' and last.get('tier') == tier


SKIP_CLASSES = ('too_large', 'repeated_prompt')


def marked_tiers(item, classes=SKIP_CLASSES):
    """The tiers the driver marked `failed` with one of CLASSES (no attempt) since the goal's last reset."""
    return {row['tier'] for row in since_reset(item)
            if row['state'] == 'failed' and row.get('class') in classes and row.get('tier')}


def ladder_step(item, tiers, routing):
    """(action, tier, why) of the prover ladder of a pure goal: the next attempt, else spin or reconsider."""
    rungs = ladder(item['goal_class'], tiers, routing)
    names = [name for name, _ in rungs]
    results = attempt_results(item)
    last = item['last_attempt']
    begin = max((names.index(tier) for tier in results if tier in names), default=0)
    skipped = marked_tiers(item)
    for tier, limit in rungs[begin:]:
        if tier in skipped:
            continue
        mine = results.get(tier, [])
        if not mine:
            return 'prove', tier, 'first attempt at this tier'
        if not (last and last['tier'] == tier and spent(mine) < limit):
            continue
        failure = mine[-1]
        if failure == 'compile_error':
            return 'prove', tier, 'again with the compiler error text'
        if failure == 'need_context' and not missing_context(item, tier):
            return 'prove', tier, 'again with the named context items'
        if failure == 'malformed' and mine.count('malformed') == 1:
            return 'prove', tier, 'again: the reply was malformed (bare JSON only)'
    counted = sum(spent(results.get(name, [])) for name in names)
    if counted >= SPIN_ATTEMPTS or item['resets'] >= SPIN_RESETS:
        return 'spin', None, 'ladder exhausted: %d attempts on it, %d resets' % (counted, item['resets'])
    return 'reconsider', TOP, 'every prover tier failed: reconsider the assertion that produced it (%s)' % (
        item['parent'] or '-')


def step(item, state, tiers, routing):
    """(action, tier, why) for one obligation, or None when nothing is due."""
    st = item['state']
    if st in ('closed', 'running'):
        return None
    laddered = item['kind'] in ('goal', 'meaning') and item['goal_class'] not in SPATIAL_CLASSES
    if not laddered and (len(item['attempts']) >= SPIN_ATTEMPTS or item['resets'] >= SPIN_RESETS):
        return 'spin', None, '%d attempts, %d resets' % (len(item['attempts']), item['resets'])
    children = [other for other in state.values() if other['parent'] == item['id']]
    if item['kind'] == 'block':
        if st == 'derived':
            return 'rerun', None, 'new or input changed'
        if st == 'failed' and item['failure'] == 'REFUSED':
            return 'derive', None, 'render refused the block'
        if st == 'failed':
            if not children:
                return 'package', None, 'not closed, no leftover filed'
            if all(child['state'] == 'closed' for child in children):
                return 'rerun', None, 'every leftover goal closed'
            return None
        if st == 'blocked-on':
            blocker = state.get(item['blocked_by'])
            return ('rerun', None, 'blocker %s closed' % item['blocked_by']) if blocker and blocker['state'] == 'closed' else None
        return None
    if item['kind'] == 'decision':
        if st == 'waiting-decision' or (st == 'derived' and item['artifact'] is None):
            return 'decide', TOP, 'decision task: request, hint slice, derived files, checked annotations'
        if st == 'failed':
            return 'decide', TOP, 'proposal failed (%s)' % item['failure']
        if st == 'false':
            return 'owner', None, 'proposal refuted'
        if st == 'blocked-on':
            return None
        kind = store.parse_id(item['id'])[1]['decision']
        tested = any(row.get('tier') == 'machine-run' for row in since_reset(item))
        if kind in TESTED_KINDS and not tested:
            return 'test', None, 'annotations.py test on the machine-run snapshots'
        return 'check', None, 'compile the annotations and rerun'
    # goal or meaning
    if item['goal_class'] in SPATIAL_CLASSES:
        if st in ('derived', 'failed') and item['tier_attempts'].get(TOP, 0) < dict(tiers).get(TOP, 2):
            return 'diagnose', TOP, 'spatial leftover: typed diagnosis'
        return 'reconsider', TOP, 'diagnosis failed: reconsider %s' % (item['parent'] or '-')
    if st == 'false':
        return 'owner', None, 'statement false (counterexample: %s)' % ((item['artifact'] or {}).get('path') or '-')
    if st == 'failed' and item['failure'] == 'rule_gap':
        return 'owner', None, 'rule_gap'
    if st == 'waiting-decision':
        return 'reconsider', TOP, 'reconsider %s' % (item['parent'] or '-')
    if st == 'blocked-on':
        blocker = state.get(item['blocked_by'])
        if not blocker or blocker['state'] != 'closed':
            return None
    if names_address(item):
        return 'owner', None, 'class ADDRESS: names a code address'
    if not any(row.get('tier') == 'falsify' for row in since_reset(item)):
        return 'falsify', None, 'falsity check first'
    return ladder_step(item, tiers, routing)


def next_items(run, function=None, limit=None, tiers=None, routing=None):
    tiers = load_tiers() if tiers is None else tiers
    routing = load_routing() if routing is None else routing
    order = [name for name, _ in tiers]
    state = store.fold(store.read_events(run))
    items = []
    for item in state.values():
        if function and item['function'] != function:
            continue
        found = step(item, state, tiers, routing)
        if found:
            action, tier, why = found
            rank = order.index(tier) if tier in order else len(order)
            items.append((GROUPS[action], rank, len(items), item['id'], action, tier, why))
    items.sort()
    return [(identifier, action, tier, why) for _, _, _, identifier, action, tier, why in items][:limit]


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__.split('\n')[0])
    commands = parser.add_subparsers(dest='command', required=True)
    command = commands.add_parser('next')
    command.add_argument('--function', required=True)
    command.add_argument('--run', type=Path)
    command.add_argument('--limit', type=int, default=20)
    options = parser.parse_args(argv)
    run = options.run or store.default_run(options.function)
    lines = ['%s %s%s %s' % (identifier, action, ' tier=' + tier if tier else '', why)
             for identifier, action, tier, why in next_items(run, options.function, options.limit)]
    text = ''.join(line + '\n' for line in lines)
    sys.stdout.write(text)
    store.record_coordinator_read(run, 'route.next', text)
    return 0


if __name__ == '__main__':
    sys.exit(main())
