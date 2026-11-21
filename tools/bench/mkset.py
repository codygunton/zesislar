#!/usr/bin/env python3
"""Write a BENCH set with every rendered caller of one function and a CPU cap per member.

usage: mkset.py FUNCTION CALLERS_DIR --name NAME [--output PATH] [--cfg PATH] [--overlays-from SET]
                [--claim-gib N] [--limit-gib N] [--jobs N]

CALLERS_DIR is a generated caller directory (tools/block/generated/<dir>, with CALLERS.json). Every
row of CALLERS.json with status "rendered" becomes a member; inlined return blocks are not callers.
A member's "cpu_seconds" is
    min(1200, 120 + 45 x instructions + 100 x successor entries + 3 x successor-entry binders),
the instructions being the CFG rows (build/stock-zisk/cfg.json) the caller steps through: from its pc
to the start of a successor caller, through inlined blocks, ending at a call, a jump out of the
function or a `ret`/`jr` (a caller with no successor premise counts to its return). The successor
entries are the generated entry premises of the caller (`instr_pre ... <module>.fp_machineAt<case>`
in CALLERS.json "preconditions", and the generated machine-return package
`instr_pre ... <module>.fp_machineReturn<slot>` of a block that ends at the function's return): on
sealed entries a short block still proves each successor's whole entry, so the binders of the
successor entry definitions (every `∃` binder of the definitions `fp_machineAt<case>*` or
`fp_machineReturn<slot>*` in that module) count. The blocks of HEAVY (plan steps 1.4, 2.2,
issue #316) get 2400 CPU-s instead. A member claims ceil(1.25 x its measured peak) GiB when
MEASURED_PEAK_GIB lists it, else --claim-gib (default 3).
A function that is not on main needs its overlay: --overlays-from copies the overlay of that name
from an existing set (and --cfg points at a CFG that has the function).
Writes tools/bench/sets/NAME.json unless --output is given.
"""
import argparse
from datetime import date
from fnmatch import fnmatch
import json
import math
from pathlib import Path
import re
import sys

BENCH = Path(__file__).resolve().parent
ROOT = BENCH.parent.parent
CPU_FLOOR, CPU_PER_INSTRUCTION, CPU_CEILING = 120, 45, 1200
# Calibrated on the sealed entries (lanes 1.5, 2.3, 2.2, issue #316): every block measured closing
# gets at least 1.5 x its largest measured CPU-s (or the ceiling), e.g. decodeParentHeader 039c (917
# CPU-s, 5 instructions, 279 successor binders) and nextUint64 0058 (353, 3 instructions, 67 binders).
CPU_PER_SUCCESSOR, CPU_PER_SUCCESSOR_BINDER = 100, 3
HEAVY_CPU = 2400
CLAIM_MARGIN = 1.25
# Blocks whose measured runs need more than the formula (plan steps 1.4 and 2.2, issue #316): case
# patterns per function. nextUint64 0070 and 00a4 close above their formula caps (480, 345): 454 and
# 370 CPU-s on an idle host, 626 and 528 on a loaded one (lane 1.3).
HEAVY = {'decodeParentHeader': ['0000', '0088', '0094', '00a8', '0270', '0408', '04ec', '0514_slot*'],
         'nextUint64': ['0000', '0070', '00a4']}
# Largest measured peak (GiB) of the blocks that peak above 2.4 GiB on the sealed entries, closed or at
# their cap (PH-ALL and NU-ALL runs of lanes 1.5, 2.2 and 2.3, issue #316); the others fit --claim-gib.
MEASURED_PEAK_GIB = {
    'decodeParentHeader': {'0000': 7.01, '0048': 3.67, '0088': 3.69, '0094': 3.67, '00a8': 3.57, '00ec': 2.65,
                           '01e4': 4.28, '0218': 2.61, '0244': 4.09, '0270': 3.22, '02d0': 3.19, '0300': 3.96,
                           '0334': 4.25, '039c': 4.06, '03bc': 7.12, '0408': 3.94, '046c': 2.94, '04b0': 2.48,
                           '04ec': 4.46, '04f8': 3.11, '0514_slot0': 2.44, '0514_slot2': 3.77,
                           '0514_slot4': 4.24, '0570': 3.02, '0274_slot0': 3.00, '0274_slot1': 3.35,
                           '0274_slot2': 6.12, '0274_slot3': 6.94, '0274_slot4': 6.00, '0274_slot5': 5.24,
                           '0274_slot6': 6.53},
    'nextUint64': {'0000': 3.35, '0070': 3.16, '00a4': 4.37, '00b8': 2.84}}
ENTRY_PREMISE = re.compile(r'instr_pre \S+ \(((?:[A-Za-z0-9_]+\.)+)(fp_machine(?:At|Return)[A-Za-z0-9_]+) ')
BINDER_GROUP = re.compile(r'∃((?:\s*\([^():]+:[^()]+\))+)\s*,')
BINDER = re.compile(r'\(([^():]+):')


def successor_entries(root, preconditions):
    """(module file, entry name) of every generated entry premise of a caller."""
    out = []
    for premise in preconditions:
        match = ENTRY_PREMISE.match(premise)
        if match:
            out.append((root / (match.group(1).rstrip('.').replace('.', '/') + '.v'), match.group(2)))
    return out


def entry_binders(module, name):
    """Number of `∃` binders in the definitions `name` and `name_*` of an entry module."""
    if not module.is_file():
        raise SystemExit('mkset: no entry module %s' % module)
    count = 0
    for definition in re.split(r'\n(?=Definition )', module.read_text()):
        if re.match(r'Definition %s(?:_\S*)? ' % re.escape(name), definition):
            count += sum(len(BINDER.findall(group.group(1))) for group in BINDER_GROUP.finditer(definition))
    return count


def member_claim(function, case, claim_gib):
    peak = MEASURED_PEAK_GIB.get(function, {}).get(case)
    return claim_gib if peak is None else max(claim_gib, math.ceil(CLAIM_MARGIN * peak))


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
    root = callers_dir.parents[3]
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
        claim = member_claim(function, row['case'], claim_gib)
        if is_heavy(function, row['case']):
            member.update(cpu_seconds=HEAVY_CPU, claim_gib=claim,
                          why='%d instructions; heavy block of plan steps 1.4 and 2.2: %d CPU-s, claim %d GiB'
                          % (count, HEAVY_CPU, claim))
        else:
            entries = successor_entries(root, row.get('preconditions', []))
            binders = sum(entry_binders(module, name) for module, name in entries)
            cap = min(CPU_CEILING, CPU_FLOOR + CPU_PER_INSTRUCTION * count + CPU_PER_SUCCESSOR * len(entries)
                      + CPU_PER_SUCCESSOR_BINDER * binders)
            member.update(cpu_seconds=cap, claim_gib=claim,
                          why='%d instructions, %d successor entries, %d successor binders: cap min(%d, %d + %d x %d'
                              ' + %d x %d + %d x %d) = %d CPU-s, claim %d GiB'
                          % (count, len(entries), binders, CPU_CEILING, CPU_FLOOR, CPU_PER_INSTRUCTION, count,
                             CPU_PER_SUCCESSOR, len(entries), CPU_PER_SUCCESSOR_BINDER, binders, cap, claim))
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
    parser.add_argument('--claim-gib', type=int, default=3)
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
