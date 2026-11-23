#!/usr/bin/env python3
"""Checked answers to the requests of derive.py: the annotation file of one function (plan A6).

    annotations.py compile --function F     write tools/block/functions/F.json from F.annotations.json
    annotations.py check [--function F]     fail when a profile differs from its compiled annotations
    annotations.py test --function F --run RUN [--row ID ...]
                                            evaluate the rows' facts on the machine-run snapshots

The annotation file `tools/block/functions/<F>.annotations.json`, schema `zesu.annotations.v1`:

    {"schema": "zesu.annotations.v1", "function": F, "symbol": ELF symbol,
     "profile": {...profile keys copied as they are...}, "rows": [ROW, ...]}

A ROW: `id`, `request` (the derive.py request id it answers), `at` {`pc` (`+0xOFFSET` from the symbol, or
`SYMBOL+0xOFFSET`), `boundary`, and for a loop cut `predecessor` (the block of its entry edge)},
`binders` [{`name`, `register`?, `role`?, `exec`?}], `resources` [Iris text], `facts` [{`coq`, `role`,
...}], `placement`, `author` {`tier`}, and for a loop cut `visible` (history patterns it shows).

The compiled profile keys, by `boundary`:
  entry            `domain_component` = ⌜fact /\\ ...⌝; its `predicates` [{`name`, `owner`}] become
                   `opaque_predicates` {name: {owner, name}}: the contract's opaque predicates the
                   entry renderer writes as `owner.name args` (render_fp301_entries.py)
  loop_cut         `loop_heads` and a `loop_designs` row: `registers` (binders with a register), `index`
                   (the binder of role `index`), `facts` (role -> `kind`), `array_cursor` from
                   `placement` {`array`, `register`, `extent_reason`}, `visible`
  join             `join_designs[pc]`: a fact of role `fact` with no other key is its text, else its object
  call_site        a `calls` row: the row's `call` object with `call_site_pc`. Its `opaque` rows
                   [{`spec`, `use`: framed | consumed | produced, `caller`: [...]}] name spec resources in
                   the spec's text and, for a consumed one, the caller components it takes; its `returns`
                   rows [{`index`, `register`}] name the returned registers the continuation reads
                   (call_boundary.call_return_seed)
  call_return      the `return_facts` of the call whose `return_site_pc` is `pc` (role -> `kind`)
  function_return  a `function_returns` row: `return_instruction_pc` and `return_fact` (True without facts)
  access           an `access_placements` row: `pc` and `placement` {`array`, `index`, `scale`, `offset`},
                   which the forward pass reads (symbolic_state.ACCESS_PLACEMENTS)
The compiled profile carries `generated_from` {`path`, `sha256`}. The three hand-written profiles have
no annotation file.

`test` instantiates each row's binders from the snapshots `RUN/exec/<input>/STATE-<oooo>.json` at its pc
(schema `oblig-exec-snapshot/1`): a binder with a `register` takes that register at the visit; a binder
with `exec` takes that Coq term. In facts and `exec` terms, `{xN}` (or an ABI name) is the register at
the function entry (STATE-0000.json, first visit) and `{reg:xN}` the register at the visit; `{bytes:NAME}`
is the snapshot memory range NAME as a byte list. Each fact is evaluated with
`Eval vm_compute in bool_decide (...)`. One false fact rejects the row and names its input; a fact
that does not elaborate (a contract name the snapshot cannot give) is reported unchecked.
"""
from pathlib import Path
import argparse
import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[2]
FUNCTIONS = ROOT / 'tools/block/functions'
SCHEMA = 'zesu.annotations.v1'
BOUNDARIES = ('entry', 'loop_cut', 'join', 'call_site', 'call_return', 'function_return', 'access')
GENERATED_KEYS = ('loop_designs', 'join_designs', 'calls', 'function_returns', 'access_placements',
                  'domain_component', 'opaque_predicates', 'generated_from')
OPAQUE_USES = ('framed', 'consumed', 'produced')
PC = re.compile(r'(?:[^+\s]+)?\+0x[0-9a-f]+')
ABI = ['zero', 'ra', 'sp', 'gp', 'tp', 't0', 't1', 't2', 's0', 's1', 'a0', 'a1', 'a2', 'a3', 'a4', 'a5', 'a6',
       'a7', 's2', 's3', 's4', 's5', 's6', 's7', 's8', 's9', 's10', 's11', 't3', 't4', 't5', 't6']
HEADER = ('From stdpp Require Import bitvector.definitions decidable.\n'
          'From Coq Require Import ZArith List.\nImport ListNotations.\nLocal Open Scope Z_scope.\n')


class AnnotationError(ValueError):
    """The annotation file breaks its schema."""


def annotation_path(function):
    return FUNCTIONS / (function + '.annotations.json')


def profile_path(function):
    return FUNCTIONS / (function + '.json')


def validate(data):
    if data.get('schema') != SCHEMA:
        raise AnnotationError('schema must be ' + SCHEMA)
    for key in ('function', 'symbol', 'profile', 'rows'):
        if key not in data:
            raise AnnotationError('the annotation file lacks ' + key)
    ids = set()
    for row in data['rows']:
        if row.get('id') in ids or not row.get('id'):
            raise AnnotationError('a row id is missing or repeated: %s' % row.get('id'))
        ids.add(row['id'])
        at = row.get('at') or {}
        if at.get('boundary') not in BOUNDARIES:
            raise AnnotationError('%s: boundary must be one of %s' % (row['id'], ', '.join(BOUNDARIES)))
        if not isinstance(at.get('pc'), str) or not PC.fullmatch(at['pc']):
            raise AnnotationError('%s: pc must be +0xOFFSET or SYMBOL+0xOFFSET' % row['id'])
        for fact in row.get('facts', []):
            if not isinstance(fact.get('coq'), str) or not fact.get('role'):
                raise AnnotationError('%s: every fact has `coq` and `role`' % row['id'])
    generated = set(GENERATED_KEYS) & set(data['profile'])
    if generated:
        raise AnnotationError('the profile part holds compiled keys: ' + ', '.join(sorted(generated)))
    return data


def _extras(fact):
    return {key: value for key, value in fact.items() if key not in ('coq', 'role')}


def _kind_fact(fact):
    """A loop or return fact of the profile: `kind` from the role, then its other keys."""
    return {'kind': fact['role'], **_extras(fact), 'coq': fact['coq']}


def _join_fact(fact):
    extras = _extras(fact)
    if fact['role'] == 'fact' and not extras:
        return fact['coq']
    return {'coq': fact['coq'], **extras}


def _check_call(row):
    """The shape of a call row's `opaque` and `returns` rows (call_boundary consumes them)."""
    for item in row['call'].get('opaque', []):
        if not isinstance(item.get('spec'), str) or item.get('use') not in OPAQUE_USES:
            raise AnnotationError('%s: an opaque row has `spec` and a `use` among %s'
                                  % (row['id'], ', '.join(OPAQUE_USES)))
        callers = item.get('caller', [])
        if item['use'] == 'consumed' and not callers or item['use'] == 'produced' and callers \
                or not all(isinstance(text, str) for text in callers):
            raise AnnotationError('%s: a consumed opaque row names its caller resources, a produced one none'
                                  % row['id'])
    for item in row['call'].get('returns', []):
        if not isinstance(item.get('index'), int) or not re.fullmatch(r'x(1[0-7])', str(item.get('register'))):
            raise AnnotationError('%s: a returns row has an integer `index` and an argument register' % row['id'])


def compile_profile(data, source=None):
    """The function profile of an annotation file (see the module text)."""
    validate(data)
    profile = json.loads(json.dumps(data['profile']))
    profile.setdefault('function', data['function'])
    profile.setdefault('symbol', data['symbol'])
    heads = list(profile.get('loop_heads', []))
    loop_designs, join_designs, calls, returns, placements = [], {}, [], [], []
    rows = data['rows']
    for row in rows:
        at, boundary = row['at'], row['at']['boundary']
        facts = row.get('facts', [])
        if boundary == 'entry':
            if facts:
                profile['domain_component'] = '⌜' + ' /\\ '.join(fact['coq'] for fact in facts) + '⌝'
            for predicate in row.get('predicates', []):
                if set(predicate) != {'name', 'owner'}:
                    raise AnnotationError('%s: a predicate row has exactly `name` and `owner`' % row['id'])
                profile.setdefault('opaque_predicates', {})[predicate['name']] = dict(predicate)
        elif boundary == 'loop_cut':
            if at['pc'] not in heads:
                heads.append(at['pc'])
            design = {'head': at['pc']}
            if at.get('predecessor'):
                design['entry_predecessor'] = at['predecessor']
            design['registers'] = {binder['register']: binder['name'] for binder in row.get('binders', [])
                                   if binder.get('register')}
            index = [binder['name'] for binder in row.get('binders', []) if binder.get('role') == 'index']
            if index:
                design['index'] = index[0]
            design['facts'] = [_kind_fact(fact) for fact in facts]
            placement = row.get('placement')
            if placement:
                design['array_cursor'] = {'register': placement['register'], 'array': placement['array'],
                                          'extent_reason': placement['extent_reason']}
            if 'visible' in row:
                design['visible'] = list(row['visible'])
            loop_designs.append(design)
        elif boundary == 'join':
            join_designs.setdefault(at['pc'], []).extend(_join_fact(fact) for fact in facts)
        elif boundary == 'call_site':
            if 'call' not in row:
                raise AnnotationError('%s: a call_site row carries its `call` object' % row['id'])
            _check_call(row)
            calls.append({**row['call'], 'call_site_pc': at['pc']})
        elif boundary == 'function_return':
            returns.append({'return_instruction_pc': at['pc'],
                            'return_fact': ' /\\ '.join(fact['coq'] for fact in facts) if facts else True})
        elif boundary == 'access':
            placement = row.get('placement') or {}
            missing = {'array', 'index', 'scale', 'offset'} - set(placement)
            if missing:
                raise AnnotationError('%s: placement lacks %s' % (row['id'], ', '.join(sorted(missing))))
            placements.append({'pc': at['pc'], **{key: placement[key] for key in ('array', 'index', 'scale', 'offset')}})
    for row in rows:
        if row['at']['boundary'] != 'call_return':
            continue
        owners = [call for call in calls if call.get('return_site_pc') == row['at']['pc']]
        if len(owners) != 1:
            raise AnnotationError('%s: no single call_site row returns to %s' % (row['id'], row['at']['pc']))
        owners[0].setdefault('return_facts', []).extend(_kind_fact(fact) for fact in row.get('facts', []))
    if heads:
        profile['loop_heads'] = heads
    for key, value in (('loop_designs', loop_designs), ('join_designs', join_designs), ('calls', calls),
                       ('function_returns', returns), ('access_placements', placements)):
        if value:
            profile[key] = value
    if source is not None:
        profile['generated_from'] = {'path': str(Path(source).resolve().relative_to(ROOT)),
                                     'sha256': hashlib.sha256(Path(source).read_bytes()).hexdigest()}
    return profile


def render_profile(profile):
    return json.dumps(profile, indent=2) + '\n'


def cmd_compile(function):
    source = annotation_path(function)
    profile = compile_profile(json.loads(source.read_text()), source)
    profile_path(function).write_text(render_profile(profile))
    print('annotations: wrote %s from %s' % (profile_path(function).relative_to(ROOT), source.relative_to(ROOT)))
    return 0


def cmd_check(functions):
    """Each annotation file's compiled profile equals the profile on disk; a profile that names
    `generated_from` has its annotation file."""
    errors = []
    names = set(functions or [path.name[:-len('.annotations.json')] for path in FUNCTIONS.glob('*.annotations.json')])
    if not functions:
        for path in FUNCTIONS.glob('*.json'):
            if not path.name.endswith('.annotations.json') and 'generated_from' in json.loads(path.read_text()):
                names.add(path.stem)
    for function in sorted(names):
        source, target = annotation_path(function), profile_path(function)
        if not source.exists():
            errors.append('%s: generated_from names no annotation file' % target.relative_to(ROOT))
            continue
        try:
            expected = compile_profile(json.loads(source.read_text()), source)
        except AnnotationError as error:
            errors.append('%s: %s' % (source.relative_to(ROOT), error))
            continue
        if not target.exists() or json.loads(target.read_text()) != expected:
            errors.append('%s differs from the compiled %s; run annotations.py compile --function %s'
                          % (target.relative_to(ROOT), source.relative_to(ROOT), function))
    for error in errors:
        print('annotations check: ' + error, file=sys.stderr)
    print('annotations check: %d profiles, %d errors' % (len(names), len(errors)))
    return 1 if errors else 0


# ---------------------------------------------------------------- machine-run test

def coqc_command():
    """coqc from $COQC, PATH, or the Islaris opam switch the Makefile names ($ISLARIS_REPO, ~/islaris)."""
    for candidate in (os.environ.get('COQC'), shutil.which('coqc'),
                      str(Path(os.environ.get('ISLARIS_REPO', Path.home() / 'islaris')) / '_opam/bin/coqc')):
        if candidate and Path(candidate).exists():
            return candidate
    return None


def register_key(name):
    if re.fullmatch(r'x\d+', name):
        return ABI[int(name[1:])]
    return 's0' if name == 'fp' else name


def offset_key(pc):
    """`oooo` of a `+0xOFFSET` pc (the snapshot file name)."""
    if not pc.startswith('+0x'):
        raise AnnotationError('test reads offsets of the function itself; got ' + pc)
    return format(int(pc[1:], 16), '04x')


def bv(value):
    return '(BV 64 %d)' % (value % (1 << 64))


def byte_list(row):
    data = bytes.fromhex(row['hex'])
    return '[' + '; '.join('BV 8 %d' % byte for byte in data) + ']'


def substitute(text, entry, regs, memory):
    def replace(match):
        token = match[1]
        if token.startswith('reg:'):
            return bv(regs[register_key(token[4:])])
        if token.startswith('bytes:'):
            rows = [row for row in memory if row['name'] == token[6:]]
            if len(rows) != 1:
                raise KeyError('no memory range ' + token[6:])
            return byte_list(rows[0])
        return bv(entry[register_key(token)])
    return re.sub(r'\{((?:reg:|bytes:)?[\w#.-]+)\}', replace, text)


def fact_term(row, fact, entry, visit):
    """The closed Coq term `let <binders> in bool_decide (<fact>)` of one visit."""
    regs, memory = visit['regs'], visit.get('memory', [])
    lets = []
    for binder in row.get('binders', []):
        if binder.get('register'):
            lets.append('let %s := %s in' % (binder['name'], bv(regs[register_key(binder['register'])])))
        elif binder.get('exec'):
            lets.append('let %s := %s in' % (binder['name'], substitute(binder['exec'], entry, regs, memory)))
    return ' '.join(lets + ['bool_decide (%s)' % substitute(fact['coq'], entry, regs, memory)])


def evaluate(terms, coqc, directory, split=True):
    """[True | False | error text] per term: one coqc run, then (with `split`) one per term after an
    error; without `split`, None after an error."""
    def run(batch, name):
        path = Path(directory) / name
        path.write_text(HEADER + ''.join('Eval vm_compute in (%s).\n' % term for term in batch))
        result = subprocess.run([coqc, path.name], cwd=directory, capture_output=True, text=True)
        values = re.findall(r'=\s*(true|false)\s*:\s*bool', result.stdout)
        return result.returncode, values, (result.stdout + result.stderr)[-800:]
    code, values, output = run(terms, 'Snapshot.v')
    if code == 0 and len(values) == len(terms):
        return [value == 'true' for value in values]
    if not split:
        return None
    results = []
    for index, term in enumerate(terms):
        code, values, output = run([term], 'Snapshot_%d.v' % index)
        results.append(values[0] == 'true' if code == 0 and len(values) == 1 else output.strip())
    return results


def snapshots(run, row):
    """[(input id, entry registers, visit)] at the row's pc, over every input dir of RUN/exec.

    The entry registers (`{xN}`) are those at the function entry (STATE-0000.json), and for a loop cut
    those at the loop entry: the first visit of the head after the latest visit of its entry predecessor
    (STATE-<predecessor>.json; without it, the first visit of the head)."""
    at = row['at']
    key = offset_key(at['pc'])
    loop = at['boundary'] == 'loop_cut'
    found = []
    for directory in sorted(Path(run, 'exec').glob('*/')):
        state = directory / ('STATE-%s.json' % key)
        if not state.exists():
            continue
        data = json.loads(state.read_text())
        visits = sorted(data['visits'], key=lambda visit: visit.get('insn', 0))
        if loop:
            predecessor = directory / ('STATE-%s.json' % offset_key(at['predecessor'])) \
                if at.get('predecessor') else None
            marks = sorted(visit.get('insn', 0) for visit in json.loads(predecessor.read_text())['visits']) \
                if predecessor is not None and predecessor.exists() else []
            for visit in visits:
                before = [mark for mark in marks if mark < visit.get('insn', 0)]
                start = next(other for other in visits if other.get('insn', 0) > before[-1]) if before else visits[0]
                found.append((data.get('input', directory.name), start['regs'], visit))
            continue
        entry = directory / 'STATE-0000.json'
        if not entry.exists():
            continue
        entry_regs = json.loads(entry.read_text())['visits'][0]['regs']
        for visit in visits:
            found.append((data.get('input', directory.name), entry_regs, visit))
    return found


def test_rows(data, run, row_ids=None, coqc=None):
    """{'verdict': 'passed' | 'rejected' | 'untested', ...} over the selected rows."""
    validate(data)
    coqc = coqc or coqc_command()
    if coqc is None:
        raise SystemExit('annotations test: no coqc (set COQC or ISLARIS_REPO)')
    rows = [row for row in data['rows'] if row_ids is None or row['id'] in row_ids]
    checked, unchecked, untested = 0, [], []
    with tempfile.TemporaryDirectory() as directory:
        for row in rows:
            if not row.get('facts'):
                continue
            visits = snapshots(run, row)
            if not visits:
                untested.append(row['id'])
                continue
            facts = list(row['facts'])

            def terms_of(facts):
                return [fact_term(row, fact, entry, visit) for _, entry, visit in visits for fact in facts]
            values = evaluate(terms_of(facts), coqc, directory, split=False)
            if values is None:
                # A fact that does not elaborate on the first visit stays unchecked on every visit.
                _, entry, visit = visits[0]
                first = evaluate([fact_term(row, fact, entry, visit) for fact in facts], coqc, directory)
                for fact, value in zip(list(facts), first):
                    if not isinstance(value, bool):
                        unchecked.append({'row': row['id'], 'fact': fact['coq'], 'error': value})
                        facts.remove(fact)
                values = evaluate(terms_of(facts), coqc, directory) if facts else []
            # Visit order, then fact order: the first false fact names the input, its visit and the fact.
            for index, value in enumerate(values):
                (input_id, _, visit), fact = visits[index // len(facts)], facts[index % len(facts)]
                if value is True:
                    checked += 1
                elif value is False:
                    return {'verdict': 'rejected', 'row': row['id'], 'input': input_id,
                            'visit': visit.get('visit'), 'pc': row['at']['pc'], 'fact': fact['coq']}
                else:
                    unchecked.append({'row': row['id'], 'input': input_id, 'fact': fact['coq'], 'error': value})
    return {'verdict': 'passed' if checked else 'untested', 'checked': checked, 'unchecked': unchecked,
            'untested_rows': untested}


def main():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    commands = parser.add_subparsers(dest='command', required=True)
    compile_parser = commands.add_parser('compile')
    compile_parser.add_argument('--function', required=True)
    check_parser = commands.add_parser('check')
    check_parser.add_argument('--function', action='append')
    test_parser = commands.add_parser('test')
    test_parser.add_argument('--function', required=True)
    test_parser.add_argument('--run', required=True, type=Path)
    test_parser.add_argument('--row', action='append')
    test_parser.add_argument('--annotations', type=Path, help='an annotation file other than the committed one')
    options = parser.parse_args()
    if options.command == 'compile':
        return cmd_compile(options.function)
    if options.command == 'check':
        return cmd_check(options.function)
    source = options.annotations or annotation_path(options.function)
    result = test_rows(json.loads(source.read_text()), options.run, options.row)
    print(json.dumps(result, indent=1))
    return 1 if result['verdict'] == 'rejected' else 0


if __name__ == '__main__':
    sys.exit(main())
