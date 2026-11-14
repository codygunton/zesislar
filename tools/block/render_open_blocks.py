"""Render the block obligations of one function's compliance theorem.

Input: the function profile and its caller table (render_function_callers.py,
CALLERS.json). Output: one Rocq module of declarations only, consumed by the
hand-written composition over the Automation2 block table:

- `<Stem>OpenBlocks`, a Prop record with one named field per block whose proof
  is not closed. The compliance theorem takes the record as a premise, so its
  fields are the remaining work.
- `<Stem>ClosedBlocks` and its inhabitant `<stem>ClosedBlocks`, built from the
  compiled caller lemmas (`DesignedBoundary_*`) of the closed blocks.
- `<stem>BlockTable`, the block table: every rendered entry with the contract
  continuation as its K.

A block is closed when the closed-proofs directory compiles its caller (a copy
rule for `Caller<block>.v` in that directory's dune file). A rendered block's
field is the caller statement, for every K. A block without a caller but with
an entry gets the contract continuation as K; its field covers the blocks
without entries that it reaches (they have no slot in the table), and its
premises are the table entries those blocks reach and the callee specs of their
call sites. No proof script is written.

Usage: render_open_blocks.py --function NAME --callers CALLERS.json
       --stem ParentHeader --boundary MODULE --output FILE [--closed-dir DIR] [--check]
"""
from pathlib import Path
import argparse, json, re, sys

sys.path.insert(0, str(Path(__file__).resolve().parent))
from function_profiles import load_profile

ROOT = Path(__file__).resolve().parents[2]
CORE_IMPORT = 'Require Import ZesuSsz.Automation2.All.'


def lower_first(text):
    return text[:1].lower() + text[1:]


def closed_cases(closed_dir):
    """The blocks whose callers the closed-proofs directory compiles."""
    if closed_dir is None:
        return set()
    dune = ROOT / closed_dir / 'dune'
    if not dune.exists():
        return set()
    return set(re.findall(r'\(targets Caller(\w+)\.v\)', dune.read_text()))


def call_premises(profile, start, end):
    """The callee spec premises of the call sites in [start, end), in profile order."""
    premises, modules = [], []
    for call in profile.get('calls', []) + profile.get('tail_calls', []):
        if start <= int(call['call_site_pc'], 16) < end:
            modules.append(call['spec_module'])
            premises.append('instr_pre ' + call['callee_pc'] + ' ('
                            + call['spec_module'] + '.' + call['spec'] + ')%I')
    return premises, modules


def plan(profile, rows, closed, entry_exists):
    """Return the open fields, the closed fields and the table slots, in address order."""
    by_case = {row['case']: row for row in rows}
    order = sorted(by_case, key=lambda case: int(by_case[case]['pc'], 16))
    ends = {case: (int(by_case[after]['pc'], 16) if after else 1 << 64)
            for case, after in zip(order, order[1:] + [None])}
    entries = [case for case in order if entry_exists(case)]
    open_fields, closed_fields = [], []
    for case in entries:
        row = by_case[case]
        if row['status'] == 'rendered':
            if case in closed:
                closed_fields.append((case, row, None))
            else:
                open_fields.append((case, row, None))
            continue
        # No caller: the block and the entry-less blocks it reaches form one obligation.
        region, successors, stack = [], [], [case]
        while stack:
            block = stack.pop()
            if block in region:
                continue
            region.append(block)
            for name in by_case[block]['successors']:
                if not entry_exists(name):
                    stack.append(name)
                elif name not in successors:
                    successors.append(name)
        address = lambda block: int(by_case[block]['pc'], 16)
        open_fields.append((case, row, {'region': sorted(region, key=address),
                                        'successors': sorted(successors, key=address),
                                        'ends': ends}))
    return entries, open_fields, closed_fields, by_case


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--function', required=True)
    parser.add_argument('--callers', type=Path, required=True)
    parser.add_argument('--stem', required=True)
    parser.add_argument('--boundary', required=True)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--closed-dir')
    parser.add_argument('--check', action='store_true', help='fail if OUTPUT differs from a fresh render')
    options = parser.parse_args()
    profile = load_profile(options.function)
    rows = json.loads(options.callers.read_text())['rows']
    generated = ROOT / profile.generated_directory
    entry_exists = lambda case: (generated / ('Pilot' + case + 'Entries.v')).exists()
    closed = closed_cases(options.closed_dir)
    entries, open_fields, closed_fields, by_case = plan(profile, rows, closed, entry_exists)
    stem, low = options.stem, lower_first(options.stem)
    continuation = low + 'Continuation args returnAddress'

    def entry(case):
        return profile.qualified('Pilot' + case + 'Entries', 'fp_machineAt' + case)

    def binders(pc, with_k):
        # The address tag lets the composition pick a slot's statement by its address.
        return ('forall (Sigma : gFunctors) `{!islaG Sigma} `{!threadG},\n    ' + low + 'BlockAt ' + pc
                + ' (forall (args : ' + profile.args_type + ') (returnAddress : Z)'
                + (' (K : iProp Sigma)' if with_k else '') + ',\n')

    def statement(case, row, region):
        pc = by_case[case]['pc']
        if region is None:
            premises, k = row['preconditions'], 'K'
        else:
            premises = ['instr_pre ' + by_case[name]['pc'] + ' (' + entry(name)
                        + ' (args) (returnAddress) (' + continuation + '))%I'
                        for name in region['successors']]
            for block in region['region']:
                calls, _ = call_premises(profile, int(by_case[block]['pc'], 16), region['ends'][block])
                premises += [premise for premise in calls if premise not in premises]
            k = '(' + continuation + ')'
        return (binders(pc, region is None)
                + '    ⊢ ' + ''.join(premise + ' -∗\n      ' for premise in premises)
                + profile.selected_premise() + ' -∗\n'
                + '      instr_body ' + pc + ' ((' + entry(case) + ' (args) (returnAddress) ' + k + ') ∗ True))')

    open_statements = [statement(case, row, region) for case, row, region in open_fields]
    closed_statements = [statement(case, row, None) for case, row, _ in closed_fields]
    text = '\n'.join(open_statements + closed_statements)
    modules = [profile.qualified('Pilot' + case + 'Entries') for case in entries]
    modules += [call['spec_module'] for call in profile.get('calls', []) + profile.get('tail_calls', [])
                if call['spec_module'] + '.' in text]
    closed_module = '.'.join(Path(options.closed_dir).parts) if options.closed_dir else None
    modules += [closed_module + '.Caller' + case for case, _, _ in closed_fields]
    modules = list(dict.fromkeys(modules))

    lines = ['(* Generated by tools/block/render_open_blocks.py from',
             '   ' + str(options.callers.relative_to(ROOT) if options.callers.is_absolute() else options.callers)
             + ' and the ' + profile.name + ' profile.',
             '   Declarations only; no proof script. Regenerate, do not edit. *)',
             CORE_IMPORT, 'Require Import isla.riscv64.riscv64.',
             'From Coq Require Import Lists.List ZArith.ZArith.',
             'Require Import ZesuSsz.Automation2.BlockTable.']
    requires = profile['caller_contract_requires'] + [profile.selected_import().strip(),
                                                       'Require Import ' + options.boundary + '.']
    lines += list(dict.fromkeys(requires))
    lines += ['Require ' + module + '.' for module in modules]
    lines += ['Import ListNotations.', 'Local Open Scope Z_scope.', '']

    lines.append('(* The ' + str(len(open_fields)) + ' open blocks: each field is the statement its block proof must close. *)')
    lines.append('Record ' + stem + 'OpenBlocks : Prop := {')
    fields = []
    for (case, row, region), text in zip(open_fields, open_statements):
        note = ''
        if region is not None:
            folded = [block for block in region['region'] if block != case]
            note = ('  (* No caller (' + row.get('reason', 'refused') + ')'
                    + ('; covers ' + ', '.join(folded) + ' (no entry)' if folded else '') + '. *)\n')
        fields.append(note + '  ' + low + 'Open_' + by_case[case]['pc'][2:] + ' :\n    ' + text)
    lines.append(';\n'.join(fields))
    lines += ['}.', '']

    lines.append('(* The ' + str(len(closed_fields)) + ' closed blocks, from their compiled callers. *)')
    if closed_fields:
        lines.append('Record ' + stem + 'ClosedBlocks : Prop := {')
        lines.append(';\n'.join('  ' + low + 'Closed_' + by_case[case]['pc'][2:] + ' :\n    ' + text
                                for (case, _, _), text in zip(closed_fields, closed_statements)))
        lines += ['}.', '']
        lines.append('Definition ' + low + 'ClosedBlocks : ' + stem + 'ClosedBlocks := {|')
        lines.append(';\n'.join('  ' + low + 'Closed_' + by_case[case]['pc'][2:] + ' := @'
                                + closed_module + '.Caller' + case + '.' + row['lemma']
                                for case, row, _ in closed_fields))
        lines += ['|}.', '']
    else:
        lines += ['Record ' + stem + 'ClosedBlocks : Prop := Build_' + stem + 'ClosedBlocks {}.',
                  'Definition ' + low + 'ClosedBlocks : ' + stem + 'ClosedBlocks := Build_' + stem + 'ClosedBlocks.', '']

    lines.append('(* The block table: every rendered entry, with the contract continuation as K. *)')
    lines.append('Definition ' + low + 'BlockTable `{!islaG Sigma} `{!threadG} (args : ' + profile.args_type
                 + ') (returnAddress : Z) : blockTable Sigma := {|')
    lines.append('  block_table_code := ' + low + 'TableCode;')
    lines.append('  block_table_entries := [')
    lines.append(';\n'.join('    (' + by_case[case]['pc'] + ', (' + entry(case) + ' args returnAddress ('
                            + continuation + '))%I)' for case in entries))
    lines += ['  ] |}.', '']
    text = '\n'.join(lines)
    if options.check:
        if not options.output.exists() or options.output.read_text() != text:
            sys.exit(str(options.output) + ' is stale: rerun tools/block/render_open_blocks.py')
        return
    options.output.write_text(text)
    print(json.dumps({'open': len(open_fields), 'closed': len(closed_fields), 'entries': len(entries),
                      'without_entry': sorted(case for case in by_case if not entry_exists(case))}))


if __name__ == '__main__':
    main()
