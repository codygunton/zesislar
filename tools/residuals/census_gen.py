#!/usr/bin/env python3
"""Generate a solver-census copy of a caller file (diagnostic only).

Usage: census_gen.py CALLER.v OUT.v [--mode census|verify|residual] [--timeout S]
                     --ltacs PROBE/ltacs.json --fullnames PROBE/fullnames.json
                     [--exclude NAME,...]

Every wrapped Ltac X gets `Ltac census_body_X := <live body of X>` (the body
printed by `Print Ltac` in the caller's import context) and then
`Ltac X ::= census_wrap_X ltac:(census_body_X args)`. Solver layers run
under the diagnostic timeout and log their goal sizes; site brackets only log
entry and exit. --mode verify instead prints every census_body_X so that
verify_bodies.py can compare it with the original body."""
from pathlib import Path
import argparse, json, re, sys

HERE = Path(__file__).resolve().parent

# Solver layers: timed, measured, dumped on timeout. Names as the caller
# context's shortest unambiguous qualids (Print Ltac Signatures).
SOLVERS = [
    'Lia.lia', 'Lia.nia', 'tactics.bv_solve',
    'zesu_solve_machine_linear', 'zesu_solve_machine_bounds',
    'LinearFirstLia.zesu_lia_linear_first3',
    'Automation.Hooks.zesu_solve_machine_linear', 'Automation.Hooks.zesu_solve_machine_bounds',
    'Automation.LinearFirstLia.zesu_lia_linear_first3',
    'SearchBudget.zesu_solve_selected',
    # Uncovered non-solver cost found by census run 1 on 6a78 (74-152 s per call
    # before its bv_solve): bounded and logged like a solver layer.
    'UnionRuleComponents.zesu_region_fault_prepare',
    'Automation.UnionRuleComponents.zesu_region_fault_prepare',
    # Selected-facts solvers on main 1c0c0bfce and later (skipped when absent).
    'LinearFirstLia.zesu_lia_linked_facts', 'LinearFirstLia.zesu_lia_whole_context',
    'zesu_bv_solve_linked_facts',
]
# Site brackets beyond the Ltacs that call a solver directly.
EXTRA_BRACKETS = [
    'PureFacts.zesu_saturate_derived_facts', 'Automation.PureFacts.zesu_saturate_derived_facts',
    'zesu_branch_guard_derived_facts', 'Automation.Hooks.zesu_branch_guard_derived_facts',
]
LIB_PREFIXES = ('ZesuSsz', 'InstrSpecs')


def split_body(record):
    lines = record.split('\n')
    m = re.match(r'^Ltac (\S+)((?: [\w\']+)*) :=(.*)$', lines[0])
    if not m:
        return None
    name, args, rest = m.group(1), m.group(2).split(), m.group(3)
    body = [rest] if rest.strip() else []
    for line in lines[1:]:
        if line.startswith('Redefined by:'):
            break
        body.append(line)
    return name, args, '\n'.join(body).strip('\n')


def ident(name):
    return 'census_' + re.sub(r'\W', '_', name)


def main(argv=None):
    ap = argparse.ArgumentParser()
    ap.add_argument('caller')
    ap.add_argument('out')
    ap.add_argument('--mode', default='census', choices=['census', 'verify', 'residual'])
    ap.add_argument('--fact-limit', type=int, default=1500)
    ap.add_argument('--dump-fail', default='', help='solver layers that dump failed goals with more Props than --fail-props')
    ap.add_argument('--fail-props', type=int, default=64)
    ap.add_argument('--print-all', action='store_true',
                    help='Set Printing All before the theorem so dumped goals reparse')
    ap.add_argument('--timeout', type=int, default=5)
    ap.add_argument('--ltacs', required=True)
    ap.add_argument('--fullnames', required=True)
    ap.add_argument('--exclude', default='')
    ap.add_argument('--brackets', default='all', choices=['all', 'none'])
    a = ap.parse_args(argv)

    data = json.loads(Path(a.ltacs).read_text())
    full = json.loads(Path(a.fullnames).read_text())
    exclude = set(filter(None, a.exclude.split(',')))
    brackets = []
    if a.brackets == 'all':
        for name in sorted(data['users']):
            if name in SOLVERS or name in exclude:
                continue
            path = full.get(name) or ''
            if not path.startswith(LIB_PREFIXES):
                continue
            brackets.append(name)
        brackets += [n for n in EXTRA_BRACKETS if n in data['bodies'] and n not in exclude]
    solvers = [n for n in SOLVERS if n not in exclude and n in data['bodies']]

    src = Path(a.caller).read_text()
    m = re.search(r'^(Lemma|Theorem) ', src, re.M)
    prefix, rest = src[:m.start()], src[m.start():]
    stmt = rest[:rest.index('Proof.')]

    out = [prefix.rstrip() + '\n']
    out.append((HERE / 'core.v.in').read_text().replace('@TIMEOUT@', str(a.timeout))
               .replace('@FACTLIMIT@', str(a.fact_limit)).replace('@FAILPROPS@', str(a.fail_props)))
    dump_fail = set(filter(None, a.dump_fail.split(',')))
    if a.mode == 'residual':
        out.append((HERE / 'res.v.in').read_text())
    wrapped = []
    for kind, names in (('solver', solvers), ('bracket', brackets)):
        for name in names:
            parsed = split_body(data['bodies'][name])
            if parsed is None:
                print('skip (header)', name, file=sys.stderr)
                continue
            _, args, body = parsed
            wrapped.append((kind, name, args, body))
            out.append('Ltac %s_body %s:=\n%s.\n' % (ident(name), ''.join(x + ' ' for x in args), body))
    if a.mode == 'verify':
        out.append('Module CensusShadow. Ltac lia := idtac. Ltac nia := idtac. '
                   'Ltac bv_solve := idtac. End CensusShadow.\nImport CensusShadow.\n')
        for _, name, _, _ in wrapped:
            out.append('Print Ltac %s_body.\n' % ident(name))
    else:
        module = Path(a.out).stem
        for kind, name, args, _ in wrapped:
            fn = ('census_solver "%s" %s' % (name, 'true' if name in dump_fail else 'false')
                  if kind == 'solver' else 'census_bracket "%s"' % name)
            if not args:
                # Call the body by name from Ltac2: no Ltac1 closure is evaluated early, and
                # the redefinition stays a tactic when callers pass it as a value.
                out.append('Ltac %s ::= ltac2:(%s (fun () => Ltac1.run (Ltac1.ref [@%s; @%s_body]))).\n'
                           % (name, fn, module, ident(name)))
                continue
            out.append('Ltac %s_wrap := ltac2:(t |- %s (fun () => Ltac1.run t)).\n' % (ident(name), fn))
            # `idtac;` keeps Ltac1 from running the body while it evaluates the argument.
            out.append('Ltac %s %s::= idtac; %s_wrap ltac:(idtac; %s_body%s).\n'
                       % (name, ''.join(x + ' ' for x in args), ident(name), ident(name),
                          ''.join(' ' + x for x in args)))
        if a.print_all:
            out.append('Set Printing All.\n')
        if a.mode == 'residual':
            out.append('\n' + stmt.rstrip() + '\nProof.\n'
                       '  idtac "CENSUS BLOCK-BEGIN".\n'
                       '  zesu_block_base; try zesu_finish_residual_cascade.\n'
                       '  all: idtac "CENSUS STAGE prove-done".\n'
                       '  all: ltac2:(census_res_try ()).\n'
                       '  all: idtac "CENSUS STAGE try-done".\n'
                       '  all: ltac2:(census_res_dump "readable").\n'
                       '  Set Printing All.\n'
                       '  all: ltac2:(census_res_dump "robust").\n'
                       '  Unset Printing All.\n'
                       '  all: idtac "CENSUS STAGE dump-done".\n'
                       '  all: admit.\n'
                       'Admitted.\n')
        else:
          # No collection-off fallback: one pass, then count the goals left.
          out.append('Ltac zesu_block2 ::= zesu_block_base; try zesu_finish_residual_cascade.\n')

          out.append('\n' + stmt.rstrip() + '\nProof.\n'
                   '  idtac "CENSUS BLOCK-BEGIN".\n'
                   '  zesu_block2.\n'
                   '  all: idtac "CENSUS BLOCK tactic-done (Qed reports any goal left)".\n'
                   'Qed.\n')
    Path(a.out).write_text('\n'.join(out))
    Path(a.out + '.wrapped.json').write_text(json.dumps(
        [dict(kind=k, name=n, args=x, body=b) for k, n, x, b in wrapped], indent=1))
    print('wrapped %d solvers, %d brackets -> %s' % (
        sum(1 for w in wrapped if w[0] == 'solver'), sum(1 for w in wrapped if w[0] == 'bracket'), a.out))
    return wrapped


if __name__ == '__main__':
    main()
