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

Usage: render_loop_exits.py [--function NAME] --coqc-args ARGS.json | --check

The design table, the bound and link spellings, and the output directory come
from the function profile (`loop_exits` in tools/block/functions/NAME.json).
"""
from pathlib import Path
import argparse, hashlib, json, re, sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / 'tools/block'))
from render_fp301_statements import render_unfold_opacity
from boundary_guards import BoundaryRefused, RocqContradictionCheck, alternative_facts, contradiction_source
from function_profiles import load_profile, loop_header

PROFILE = None
FP301 = FIXTURE = HEAD_BOUND = EXIT_LINK = DESIGN = CALLERS = HEADER = SIGNATURE = None


def configure(name=None):
    """Bind the module values to one function profile."""
    global PROFILE, FP301, FIXTURE, HEAD_BOUND, EXIT_LINK, DESIGN, CALLERS, HEADER, SIGNATURE
    global FORWARD_DECLARATIONS, WITNESS_EXCLUSION
    PROFILE = load_profile(name)
    exits = PROFILE['loop_exits']
    FP301 = ROOT / PROFILE.generated_directory
    FIXTURE = ROOT / exits['fixture']
    HEAD_BOUND = exits['head_bound']
    EXIT_LINK = exits['exit_link']
    # Design table. `head` is the loop head whose class 0 is the invariant.
    # A row with `block` adds the register update and branch fact of that block.
    DESIGN = exits['design']
    CALLERS = PROFILE['callers_directory']
    HEADER = loop_header(PROFILE)
    SIGNATURE = PROFILE.telescope()
    FORWARD_DECLARATIONS = json.loads((ROOT / exits['forward_fixture']).read_text())['declarations']
    WITNESS_EXCLUSION = re.compile(exits['witness_exclusion'])


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


# The forward-pass declaration recorded in the profile's `forward_fixture` owns
# the system-register witnesses (mstatus seeds and per-instruction forward
# witnesses) that the successor entries consume. They do not depend on the loop
# path, so the exit entry keeps their binders and their facts.
FORWARD_DECLARATIONS = WITNESS_EXCLUSION = None
WITNESS = re.compile(r'\b(fp_seed_\w+|forward_witness_\w+)\b')


def forward_declaration(pc):
    # The recorded names carry the block's last four address digits.
    digits = PROFILE.pc(pc)[-4:]
    source = FORWARD_DECLARATIONS[pc]
    match = re.fullmatch(r'Definition fp_machineAt' + digits + r'_ForwardA0N0' + re.escape(SIGNATURE) +
                         r' : iProp Sigma := \(∃ (.*?), \((.*)\)\)%I\.', source)
    if match is None:
        raise ValueError('The forward declaration shape changed: ' + pc)
    return match.group(1), match.group(2)


def carry_system_witnesses(row, body):
    binders, forward_body = forward_declaration(row['pc'])
    names = re.findall(r'\((\w+) : bv 64\)', binders)
    carried = [name for name in names if WITNESS.fullmatch(name)]
    facts = [fact for fact in re.findall(r'⌜(.*?)⌝', forward_body)
             if WITNESS.search(fact) and not WITNESS_EXCLUSION.search(fact)]
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


def exit_budget(row, body):
    """A charged profile: the exit entry owns its own budget (budgets.py) instead of the head's potential."""
    if not PROFILE.charged:
        return body
    import budgets
    record = budgets.entry_budgets(PROFILE)
    potential = budgets.budget_conjunct(budgets.budget_text(record, row['head']))
    if body.count(potential) != 1:
        raise ValueError('The loop-head class does not own its potential once: ' + row['head'])
    own = budgets.resolve_registers(budgets.budget_text(record, row['pc']), [body])
    return body.replace(potential, budgets.budget_conjunct(own))


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
            + f'Require Import {PROFILE.qualified("Pilot" + pc + "Entries")}.\n'
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
    return PROFILE.qualified(f'Pilot{pc}Entries', f'fp_machineAt{pc}')


def exit_precondition(pc):
    return f'instr_pre {PROFILE.pc(pc)} ({qualified_entry(pc)} (args) (returnAddress) (K))%I'


def exit_obligations():
    """The loop-head callers (render_function_callers.py) that check each exit entry: the committed
    caller states the exit precondition; its sha256 binds the fixture row."""
    rows = []
    for row in DESIGN:
        if 'block' not in row:
            output = f'{CALLERS}/Caller{row["head"]}.v'
            caller = (ROOT / output).read_bytes()
            rows.append({'loop_head': PROFILE.pc(row['head']), 'exit_pc': PROFILE.pc(row['pc']),
                         'entry': qualified_entry(row['pc']), 'precondition': exit_precondition(row['pc']),
                         'checked_by': 'DesignedBoundary_' + PROFILE.pc(row['head'])[2:], 'output': output,
                         'sha256': hashlib.sha256(caller).hexdigest()})
            if ('\n  ' + rows[-1]['precondition'] + ' -∗\n').encode() not in caller:
                raise ValueError('The loop-head caller lacks its exit precondition: ' + output)
    return rows


def check_record(row, body):
    name = f'fp_machineAt{row["pc"]}_LoopExit'
    binders, facts = alternative_facts(f'Definition {name}{SIGNATURE} : iProp Sigma := {body}.')
    # One group with every fact: the recorded check read them together.
    source = contradiction_source(HEADER, [([binders], facts)])
    return name, binders, facts, hashlib.sha256(source.encode()).hexdigest()


def main():
    parser = argparse.ArgumentParser()
    group = parser.add_mutually_exclusive_group(required=True)
    group.add_argument('--check', action='store_true')
    group.add_argument('--coqc-args', type=Path)
    parser.add_argument('--function', default=None, help='function profile (default: decodeItem)')
    parser.add_argument('--output', type=Path, default=None,
                        help='with --coqc-args: write the exit entries under OUTPUT/sources and OUTPUT/RESULT.json '
                             '(a driver run); the committed tree, its callers and the fixture stay untouched')
    parser.add_argument('--loop-heads-dir', type=Path, default=None,
                        help='directory holding the Pilot<head>Entries.v loop-head classes (default: the committed '
                             'generated directory)')
    options = parser.parse_args()
    configure(options.function)
    global FP301
    if options.loop_heads_dir is not None:
        FP301 = options.loop_heads_dir
    fixture = json.loads(FIXTURE.read_text())
    rows = {row['output']: row for row in fixture['declarations']}
    outputs, checks = {}, []
    for row in DESIGN:
        body = exit_budget(row, exit_body(row))
        name, binders, facts, check_sha256 = check_record(row, body)
        checks.append({'definition': name, 'binders': binders, 'facts': facts,
                       'check_sha256': check_sha256, 'contradictory': None})
        for kind, source in (('Entries', entries_source(row, body)), ('Structural', structural_source(row, body))):
            output = f'{PROFILE.generated_directory}/Pilot{row["pc"]}{kind}.v'
            # A driver run (--output) writes only into OUTPUT: it needs no fixture row (a profile copy,
            # e.g. a charged variant, renders into a generated directory the fixture does not hold).
            if output not in rows and options.output is None:
                raise ValueError('The fixture has no row for ' + output)
            committed = render_unfold_opacity(source) if kind == 'Structural' else source
            outputs[output] = (source, committed)
    obligations = exit_obligations() if options.output is None else None
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
        assert obligations == fixture['exit_obligations']
        print('Loop-exit declarations match the design table.')
        return
    output_dir = options.output
    checker = RocqContradictionCheck(json.loads(options.coqc_args.read_text()), HEADER,
                                     (output_dir / 'contradiction-checks') if output_dir else
                                     ROOT / PROFILE['loop_exits']['contradiction_directory'])
    for check in checks:
        if checker(check['definition'], check['binders'], check['facts']):
            raise BoundaryRefused('The exit entry proves False and is refused: ' + check['definition'])
        check['contradictory'] = False
    if output_dir is not None:
        # A driver run: the exit entries as rendered entry cases (render_function_callers --extra-entries).
        cases = []
        for row in DESIGN:
            files = []
            for kind in ('Entries', 'Structural'):
                output = f'{PROFILE.generated_directory}/Pilot{row["pc"]}{kind}.v'
                path = output_dir / 'sources' / output
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text(outputs[output][1])
                files.append({'path': str(path), 'sha256': hashlib.sha256(path.read_bytes()).hexdigest()})
            cases.append({'pc': PROFILE.pc(row['pc']), 'status': 'source_declarations_rendered',
                          'entry': files[0], 'structural': files[1], 'qualified_entry': qualified_entry(row['pc']),
                          'source_boundary': 'loop_exits#' + row['pc'], 'proof_ran': False})
        (output_dir / 'RESULT.json').write_text(json.dumps(
            {'status': 'SOURCE_DECLARATIONS_ONLY', 'function': PROFILE.name, 'cases': cases,
             'contradiction_checks': [{key: value for key, value in check.items() if key not in ('binders', 'facts')}
                                      for check in checks]}, indent=2) + '\n')
        print('Rendered', len(outputs), 'loop-exit declarations into', output_dir)
        return
    for output, (source, committed) in outputs.items():
        rows[output]['canonical_source'] = source
        rows[output]['sha256'] = hashlib.sha256(source.encode()).hexdigest()
        rows[output]['renderer'] = 'tools/block/render_loop_exits.py'
        (ROOT / output).write_text(committed)
    fixture['contradiction_checks'] = [{key: value for key, value in check.items() if key not in ('binders', 'facts')}
                                       for check in checks]
    fixture['exit_obligations'] = obligations
    FIXTURE.write_text(json.dumps(fixture, indent=2, ensure_ascii=False) + '\n')
    print('Rendered', len(outputs), 'loop-exit declarations.')


if __name__ == '__main__':
    main()
