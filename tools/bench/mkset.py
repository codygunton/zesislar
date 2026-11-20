#!/usr/bin/env python3
"""Write a BENCH set with every rendered caller of one function and a CPU cap per member.

usage: mkset.py FUNCTION CALLERS_DIR --name NAME [--output PATH] [--cfg PATH] [--overlays-from SET]
                [--claim-gib N] [--limit-gib N] [--jobs N]

CALLERS_DIR is a generated caller directory (tools/block/generated/<dir>, with CALLERS.json). Every
row of CALLERS.json with status "rendered" becomes a member; inlined return blocks are not callers.
A member's "cpu_seconds" is min(1200, 120 + 45 x instructions), the instructions being the CFG rows
(build/stock-zisk/cfg.json) the caller steps through: from its pc to the start of a successor
caller, through inlined blocks, ending at a call, a jump out of the function or a `ret`/`jr`
(a caller with no successor premise counts to its return). The blocks of HEAVY (plan steps 1.4, 2.2,
issue #316) get 2400 CPU-s and claim 24 GiB instead. The other members claim --claim-gib (default 8).
A function that is not on main needs its overlay: --overlays-from copies the overlay of that name
from an existing set (and --cfg points at a CFG that has the function).
Writes tools/bench/sets/NAME.json unless --output is given.
"""
import argparse
from datetime import date
from fnmatch import fnmatch
import json
from pathlib import Path
import sys

BENCH = Path(__file__).resolve().parent
ROOT = BENCH.parent.parent
CPU_FLOOR, CPU_PER_INSTRUCTION, CPU_CEILING = 120, 45, 1200
HEAVY_CPU, HEAVY_CLAIM_GIB = 2400, 24
# Blocks whose measured runs need more than the formula (plan steps 1.4 and 2.2): case patterns per
# function.
HEAVY = {'decodeParentHeader': ['0000', '0088', '0094', '00a8', '0270', '0408', '04ec', '0514_slot*'],
         'nextUint64': ['0000']}


def cfg_function(cfg, function):
    """The CFG record whose name is FUNCTION or ends in .FUNCTION."""
    matches = [record for record in cfg['functions']
               if record['name'] == function or record['name'].rsplit('.', 1)[-1] == function]
    if len(matches) != 1:
        raise SystemExit('mkset: %d CFG functions named %s' % (len(matches), function))
    return matches[0]


def case_pc(case, pcs, entry):
    """The pc a case starts at: its CALLERS.json row, else entry + the case's block offset."""
    if case in pcs:
        return pcs[case]
    return entry + int(case.split('_', 1)[0], 16)


def instruction_count(record, start, stops):
    """CFG rows a caller starting at `start` steps through: it never enters a row in `stops` (the
    successor callers' starts) other than its own start, stops after a call or a jump out of the
    function, and ends at a row without successors (ret/jr)."""
    rows = {row['pc']: row for row in record['rows']}
    if start not in rows:
        raise SystemExit('mkset: pc %#x is not a CFG row of %s' % (start, record['name']))
    seen, todo = set(), [start]
    while todo:
        pc = todo.pop()
        if pc in seen or (pc in stops and pc != start) or pc not in rows:
            continue
        seen.add(pc)
        row = rows[pc]
        if row['kind'] == 'call':
            continue
        todo.extend(successor for successor in row.get('successors', []) if successor != start)
    return len(seen)


def is_heavy(function, case):
    return any(fnmatch(case, pattern) for pattern in HEAVY.get(function, []))


def members(function, callers_dir, cfg, claim_gib):
    record = cfg_function(cfg, function)
    table = json.loads((callers_dir / 'CALLERS.json').read_text())
    pcs = {row['case']: int(row['pc'], 16) for row in table['rows']}
    inlined = {row['case'] for row in table['rows'] if row['status'] == 'inlined'}
    out = []
    for row in table['rows']:
        if row['status'] != 'rendered':
            continue
        if not (callers_dir / ('Caller%s.v' % row['case'])).is_file():
            raise SystemExit('mkset: %s has no Caller%s.v' % (callers_dir, row['case']))
        stops = {case_pc(case, pcs, record['entry']) for case in row['successors'] if case not in inlined}
        count = instruction_count(record, int(row['pc'], 16), stops)
        member = {'function': function, 'callers': callers_dir.name, 'case': row['case'], 'instructions': count}
        if is_heavy(function, row['case']):
            member.update(cpu_seconds=HEAVY_CPU, claim_gib=HEAVY_CLAIM_GIB,
                          why='%d instructions; heavy block of plan steps 1.4 and 2.2: %d CPU-s, claim %d GiB'
                          % (count, HEAVY_CPU, HEAVY_CLAIM_GIB))
        else:
            cap = min(CPU_CEILING, CPU_FLOOR + CPU_PER_INSTRUCTION * count)
            member.update(cpu_seconds=cap, claim_gib=claim_gib,
                          why='%d instructions: cap min(%d, %d + %d x %d) = %d CPU-s'
                          % (count, CPU_CEILING, CPU_FLOOR, CPU_PER_INSTRUCTION, count, cap))
        member['expected_cpu'] = member['cpu_seconds']
        out.append(member)
    if not out:
        raise SystemExit('mkset: no rendered caller in %s' % callers_dir)
    return out


def build_set(options):
    callers_dir = options.callers_dir.resolve()
    if callers_dir.parent.parts[-3:] != ('tools', 'block', 'generated'):
        raise SystemExit('mkset: %s is not a directory of tools/block/generated' % options.callers_dir)
    cfg = json.loads(options.cfg.read_text())
    listed = members(options.function, callers_dir, cfg, options.claim_gib)
    overlays = []
    if options.overlays_from:
        source = json.loads(Path(options.overlays_from).read_text() if options.overlays_from.endswith('.json')
                            else (BENCH / 'sets' / (options.overlays_from + '.json')).read_text())
        overlays = [overlay for overlay in source.get('overlays', []) if overlay['name'] == options.function]
        if not overlays:
            raise SystemExit('mkset: %s has no overlay named %s' % (options.overlays_from, options.function))
    return {
        'name': options.name, 'created': date.today().isoformat(),
        'purpose': 'Every rendered caller of %s (%s), each with its own CPU cap (tools/bench/mkset.py).'
                   % (options.function, callers_dir.name),
        'caps': {'cpu_seconds': max(member['cpu_seconds'] for member in listed), 'limit_gib': options.limit_gib},
        'jobs': options.jobs, 'overlays': overlays, 'members': listed,
    }


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument('function')
    parser.add_argument('callers_dir', type=Path)
    parser.add_argument('--name', required=True)
    parser.add_argument('--output', type=Path)
    parser.add_argument('--cfg', type=Path, default=ROOT / 'build/stock-zisk/cfg.json')
    parser.add_argument('--overlays-from')
    parser.add_argument('--claim-gib', type=int, default=8)
    parser.add_argument('--limit-gib', type=int, default=24)
    parser.add_argument('--jobs', type=int, default=6)
    options = parser.parse_args(argv)
    data = build_set(options)
    output = options.output or BENCH / 'sets' / (options.name + '.json')
    output.write_text(json.dumps(data, indent=1) + '\n')
    caps = sorted({member['cpu_seconds'] for member in data['members']})
    print('%s: %d members, caps %s' % (output, len(data['members']), ', '.join(
        '%d x%d' % (cap, sum(member['cpu_seconds'] == cap for member in data['members'])) for cap in caps)))
    return 0


if __name__ == '__main__':
    sys.exit(main())
