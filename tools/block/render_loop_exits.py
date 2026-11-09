"""Render the loop-exit entries from the widened loop invariant.

A cursor loop exits when its cursor reaches the limit. The exit entry is the
loop-head class with the head bound `bv_unsigned cursor < bv_unsigned limit`
replaced by the exit link `bv_unsigned cursor = bv_unsigned limit`. A block
that follows the exit applies its register update and its branch fact to that
entry. The renderer writes declarations only, from this design table and the
committed loop-head class; it writes no proof script.

Each exit entry must be consistent: the renderer refuses it when its pure
facts prove False (boundary_guards guard 2). The loop-head caller of each
exit states the exit entry as its exit precondition, so the loop-head block
proof checks the exit obligation.

Usage: render_loop_exits.py --coqc-args ARGS.json | --check
"""
from pathlib import Path
import argparse, hashlib, json, re, sys

ROOT = Path(__file__).resolve().parents[2]
FP301 = ROOT / 'ZesuSsz/Generated/DecodeItem/FP301'
FIXTURE = ROOT / 'tools/block/fixtures/fp301-loop-successors.json'
sys.path.insert(0, str(ROOT / 'tools/block'))
from render_fp301_statements import render_unfold_opacity
from boundary_guards import BoundaryRefused, RocqContradictionCheck, alternative_facts, contradiction_source

HEAD_BOUND = '(bv_unsigned machine_x15 < bv_unsigned machine_x11)'
EXIT_LINK = '(bv_unsigned machine_x15 = bv_unsigned machine_x11)'

# Design table. `head` is the loop head whose class 0 is the invariant.
# A row with `block` adds the register update and branch fact of that block.
DESIGN = [
    {'pc': '6a38', 'head': '6a24'},
    {'pc': '6a40', 'head': '6a24', 'block': '6a38', 'update': ('x14', 'x13'), 'branch': ('ltu', 'x12', 'x14', False)},
    {'pc': '6ad8', 'head': '6ac4'},
    {'pc': '6b08', 'head': '6ac4', 'block': '6ad8', 'update': ('x14', 'x13'), 'branch': ('ltu', 'x12', 'x14', True)},
]

CALLERS = 'tools/block/generated/fp301_callers'
HEADER = '''(* Generated from FP-20261102-Level1-domain-v1. No proof script. *)
Require Import ZesuSsz.Automation2.All.
Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith NArith.NArith.
Require Import stdpp.bitvector.definitions.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Require Import ZesuSsz.Contracts.RlpDecodeItem.
Require Import ZesuSsz.Contracts.Level1.
Require Import ZesuSsz.Automation2.ByteWindowFold.
Local Open Scope Z_scope.
'''
SIGNATURE = ' `{!islaG Sigma} `{!threadG} (args : DecodeItemArgs) (returnAddress : Z)'


def loop_class(head):
    source = (FP301 / f'Pilot{head}Entries.v').read_text()
    match = re.search(r'^Definition fp_machineAt' + head + r'_LoopClass0' + re.escape(SIGNATURE) +
                      r' : iProp Sigma := (\(∃ .*\)%I)\.$', source, re.M)
    if match is None:
        raise ValueError('The loop-head class shape changed: ' + head)
    return match.group(1)


def register_value(body, register):
    match = re.search(r'"' + register + r'" ↦ᵣ RVal_Bits \((.*?) : bv 64%N\)', body)
    if match is None:
        raise ValueError('The class has no register value for ' + register)
    return match.group(1)


def strip_parens(term):
    return term[1:-1] if term.startswith('(') and term.endswith(')') else term


# The forward-pass declaration at this commit owns the system-register
# witnesses (mstatus seeds and per-instruction forward witnesses) that the
# successor entries consume. They do not depend on the loop path, so the exit
# entry keeps their binders and their facts.
FORWARD_BASE = '3505afab5'
WITNESS = re.compile(r'\b(fp_seed_\w+|forward_witness_\w+)\b')


def forward_declaration(pc):
    import subprocess
    path = f'ZesuSsz/Generated/DecodeItem/FP301/Pilot{pc}Entries.v'
    source = subprocess.run(['git', '-C', str(ROOT), 'show', FORWARD_BASE + ':' + path],
                            capture_output=True, text=True, check=True).stdout
    match = re.search(r'^Definition fp_machineAt' + pc + r'_ForwardA0N0' + re.escape(SIGNATURE) +
                      r' : iProp Sigma := \(∃ (.*?), \((.*)\)\)%I\.$', source, re.M)
    if match is None:
        raise ValueError('The forward declaration shape changed: ' + pc)
    return match.group(1), match.group(2)


def carry_system_witnesses(row, body):
    binders, forward_body = forward_declaration(row['pc'])
    names = re.findall(r'\((\w+) : bv 64\)', binders)
    carried = [name for name in names if WITNESS.fullmatch(name)]
    facts = [fact for fact in re.findall(r'⌜(.*?)⌝', forward_body)
             if WITNESS.search(fact) and not re.search(r'machine_x\d+|decodeItem|\bi\b', fact)]
    if not carried or not facts:
        raise ValueError('The forward declaration has no system witnesses: ' + row['pc'])
    prefix = '(∃ '
    if not body.startswith(prefix):
        raise ValueError('The class does not start with its telescope.')
    telescope_end = body.index(', (')
    body = body[:telescope_end] + ''.join(' (' + name + ' : bv 64)' for name in carried) + body[telescope_end:]
    if not body.endswith('⌝)%I'):
        raise ValueError('The class does not end with its pure facts.')
    return body[:-len('⌝)%I')] + ''.join(' /\\ (' + fact + ')' for fact in facts) + '⌝)%I'


def exit_body(row):
    body = loop_class(row['head'])
    if body.count(HEAD_BOUND) != 1:
        raise ValueError('The loop-head bound is not unique in ' + row['head'])
    body = body.replace(HEAD_BOUND, EXIT_LINK)
    body = carry_system_witnesses(row, body)
    if 'block' not in row:
        return body
    target, source = row['update']
    old = register_value(body, target)
    added = register_value(body, source)
    new = '(bv_add ' + added + ' ' + old + ')'
    resource = '"' + target + '" ↦ᵣ RVal_Bits (' + old + ' : bv 64%N)'
    if body.count(resource) != 1:
        raise ValueError('The updated register is not unique.')
    body = body.replace(resource, '"' + target + '" ↦ᵣ RVal_Bits (' + new + ' : bv 64%N)')
    kind, left_reg, right_reg, taken = row['branch']
    assert kind == 'ltu'
    left = register_value(body, left_reg)
    right = register_value(body, right_reg)
    if taken:
        fact = ('((bool_decide ((bv_signed (bv_zero_extend 128%N ' + left + ') >= bv_signed (bv_zero_extend 128%N '
                + right + '))%Z)) = true) /\\ ((((bv_unsigned ' + left + ') >= (bv_unsigned ' + right + ')))%Z)')
    else:
        fact = ('((negb (bool_decide ((bv_signed (bv_zero_extend 128%N ' + left + ') < bv_signed (bv_zero_extend 128%N '
                + right + '))%Z))) = true) /\\ ((((bv_unsigned ' + left + ') >= (bv_unsigned ' + right + ')))%Z)')
    if not body.endswith('⌝)%I'):
        raise ValueError('The class does not end with its pure facts.')
    return body[:-len('⌝)%I')] + ' /\\ (' + fact + ')⌝)%I'


def entries_source(row, body):
    pc = row['pc']
    return (HEADER + '\n'
            + f'Definition fp_machineAt{pc}_LoopExit{SIGNATURE} : iProp Sigma := {body}.\n\n'
            + f'Definition fp_machineAt{pc}{SIGNATURE} (K : iProp Sigma) : iProp Sigma := '
            + f'(fp_machineAt{pc}_LoopExit (args) (returnAddress) ∗ K)%I.\n')


def structural_source(row, body):
    pc = row['pc']
    exit_name = f'fp_machineAt{pc}_LoopExit'
    return (HEADER
            + f'Require Import ZesuSsz.Generated.DecodeItem.FP301.Pilot{pc}Entries.\n'
            + f'#[export] Instance {exit_name}_unfold : LithiumUnfold (@{exit_name}) := I.\n'
            + f'#[export] Typeclasses Opaque {exit_name}.\n'
            + f'#[export] Instance {exit_name}_intro{SIGNATURE} :\n'
            + f'  @ZesuSsz.Automation.Hooks.ZesuPureFactIntro Sigma ({exit_name} (args) (returnAddress))\n'
            + f'  {body} := @PreOrder_Reflexive _ _ bi.entails_po _.\n\n'
            + f'#[export] Instance fp_machineAt{pc}_unfold : LithiumUnfold (@fp_machineAt{pc}) := I.\n'
            + f'#[export] Typeclasses Opaque fp_machineAt{pc}.\n'
            + f'#[export] Instance fp_machineAt{pc}_intro{SIGNATURE} (K : iProp Sigma) :\n'
            + f'  @ZesuSsz.Automation.Hooks.ZesuPureFactIntro Sigma (fp_machineAt{pc} (args) (returnAddress) (K))\n'
            + f'  ({exit_name} (args) (returnAddress) ∗ K)%I := @PreOrder_Reflexive _ _ bi.entails_po _.\n\n')


def qualified_entry(pc):
    return f'ZesuSsz.Generated.DecodeItem.FP301.Pilot{pc}Entries.fp_machineAt{pc}'


def exit_precondition(pc):
    return f'instr_pre 0x800d{pc} ({qualified_entry(pc)} (args) (returnAddress) (K))%I'


def head_caller_source(head, exit_pc):
    """Render the loop-head caller whose exit precondition is the exit entry."""
    pc = f'800d{head}'
    return (f'''Require Import ZesuSsz.Generated.DecodeItem.FP301.Pilot{head}Entries.
Require Import ZesuSsz.Generated.DecodeItem.FP301.Pilot{head}Structural.
Require Import ZesuSsz.Generated.DecodeItem.FP301.Pilot{exit_pc}Entries.
Require Import ZesuSsz.Generated.DecodeItem.FP301.Pilot{exit_pc}Structural.
Require Import ZesuSsz.Automation2.All.
Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith NArith.NArith.
Require Import stdpp.bitvector.definitions.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Require Import ZesuSsz.Contracts.DecodeItemSelected.
Require Import ZesuSsz.Automation2.All.
Local Open Scope Z_scope.

Definition DesignedEntry_{pc}
    `{{!islaG Sigma}} `{{!threadG}} (args : DecodeItemArgs) (returnAddress : Z) (K : iProp Sigma) : iProp Sigma :=
  (({qualified_entry(head)} (args) (returnAddress) (K)) ∗
   True)%I.
Global Instance : LithiumUnfold (@DesignedEntry_{pc}) := I.
Global Typeclasses Opaque DesignedEntry_{pc}.

Lemma DesignedBoundary_{pc} `{{!islaG Sigma}} `{{!threadG}} (args : DecodeItemArgs) (returnAddress : Z) (K : iProp Sigma)  :
  {exit_precondition(head)} -∗
  {exit_precondition(exit_pc)} -∗
  decodeItemSelectedCode -∗
  instr_body 0x{pc}
    (DesignedEntry_{pc} args returnAddress K).
Proof.
  zesu_block2.
Qed.

Print Assumptions DesignedBoundary_{pc}.
''')


def exit_obligations():
    rows = []
    for row in DESIGN:
        if 'block' not in row:
            output = f'{CALLERS}/Caller{row["head"]}.v'
            source = head_caller_source(row['head'], row['pc'])
            rows.append({'loop_head': '0x800d' + row['head'], 'exit_pc': '0x800d' + row['pc'],
                         'entry': qualified_entry(row['pc']), 'precondition': exit_precondition(row['pc']),
                         'checked_by': 'DesignedBoundary_800d' + row['head'], 'output': output,
                         'sha256': hashlib.sha256(source.encode()).hexdigest(), 'source': source})
    return rows


def check_record(row, body):
    name = f'fp_machineAt{row["pc"]}_LoopExit'
    binders, facts = alternative_facts(f'Definition {name}{SIGNATURE} : iProp Sigma := {body}.')
    source = contradiction_source(HEADER, binders, facts)
    return name, binders, facts, hashlib.sha256(source.encode()).hexdigest()


def main():
    parser = argparse.ArgumentParser()
    group = parser.add_mutually_exclusive_group(required=True)
    group.add_argument('--check', action='store_true')
    group.add_argument('--coqc-args', type=Path)
    options = parser.parse_args()
    fixture = json.loads(FIXTURE.read_text())
    rows = {row['output']: row for row in fixture['declarations']}
    outputs, checks = {}, []
    for row in DESIGN:
        body = exit_body(row)
        name, binders, facts, check_sha256 = check_record(row, body)
        checks.append({'definition': name, 'binders': binders, 'facts': facts,
                       'check_sha256': check_sha256, 'contradictory': None})
        for kind, source in (('Entries', entries_source(row, body)), ('Structural', structural_source(row, body))):
            output = f'ZesuSsz/Generated/DecodeItem/FP301/Pilot{row["pc"]}{kind}.v'
            if output not in rows:
                raise ValueError('The fixture has no row for ' + output)
            committed = render_unfold_opacity(source) if kind == 'Structural' else source
            outputs[output] = (source, committed)
    obligations = exit_obligations()
    if options.check:
        for output, (source, committed) in outputs.items():
            row = rows[output]
            assert row['canonical_source'] == source, output
            assert row['sha256'] == hashlib.sha256(source.encode()).hexdigest(), output
            assert (ROOT / output).read_text() == committed, output
        recorded = {row['definition']: row for row in fixture['contradiction_checks']}
        for check in checks:
            row = recorded[check['definition']]
            assert row['check_sha256'] == check['check_sha256'] and row['contradictory'] is False, check['definition']
        assert [{key: value for key, value in row.items() if key != 'source'} for row in obligations] == fixture['exit_obligations']
        for row in obligations:
            assert (ROOT / row['output']).read_text() == row['source'], row['output']
        print('Loop-exit declarations match the design table.')
        return
    checker = RocqContradictionCheck(json.loads(options.coqc_args.read_text()), HEADER,
                                     ROOT / '_build/agents/loop-exit-contradiction-checks')
    for check in checks:
        if checker(check['definition'], check['binders'], check['facts']):
            raise BoundaryRefused('The exit entry proves False and is refused: ' + check['definition'])
        check['contradictory'] = False
    for output, (source, committed) in outputs.items():
        rows[output]['canonical_source'] = source
        rows[output]['sha256'] = hashlib.sha256(source.encode()).hexdigest()
        rows[output]['renderer'] = 'tools/block/render_loop_exits.py'
        (ROOT / output).write_text(committed)
    for row in obligations:
        (ROOT / row['output']).write_text(row['source'])
    fixture['contradiction_checks'] = [{key: value for key, value in check.items() if key not in ('binders', 'facts')}
                                       for check in checks]
    fixture['exit_obligations'] = [{key: value for key, value in row.items() if key != 'source'} for row in obligations]
    FIXTURE.write_text(json.dumps(fixture, indent=2, ensure_ascii=False) + '\n')
    print('Rendered', len(outputs), 'loop-exit declarations.')


if __name__ == '__main__':
    main()
