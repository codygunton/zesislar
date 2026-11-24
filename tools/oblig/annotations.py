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
                   `placement` {`array`, `register`, `extent_reason`}, `visible`; with `resources`,
                   `replaces` or typed binders without a register, `owned` {`binders` [{name, type}],
                   `resources` [text | {coq, length}], `replaces` [text]}: the cut's owned state is the
                   loop-entry state without the components `replaces` names (exact texts), plus
                   `resources` over those binders (loop_design.py); facts may name them
  join             `join_designs[pc]`: a fact of role `fact` with no other key is its text, else its object.
                   A row whose single effective fact is `False` (role `unreachable`) lists `pc` in
                   `unreachable_entries` (entry ⌜False⌝; refused where the forward pass reaches it); with
                   `reached: contradictory_guards` also in `unreachable_reached`: the forward pass stops
                   every path into `pc` from a predecessor block, and each such predecessor proves its
                   step in the kernel from contradictory guards; a `pc` with its own seed (a call return
                   site) keeps that seed's entry, any other gets ⌜False⌝. Its facts of role `relies_on`
                   record the guards it relies on, as documentation only (never emitted).
  call_site        a `calls` row: the row's `call` object with `call_site_pc`. Its `opaque` rows
                   [{`spec`, `use`: framed | consumed | produced, `caller`: [...]}] name spec resources in
                   the spec's text and, for a consumed one, the caller components it takes (a framed one
                   may name them too); a produced row's `as` [text | {coq, length}] states the spec resource
                   by the pieces of its LithiumUnfold, which the call block proves; its `returns`
                   rows [{`index`, `register`}] name the returned registers the continuation reads; its
                   `result_words` {byte offset: Z value} name words of the returned array the return entry
                   states and the seed reads as the value (`{argv:N}`, `{fresh:NAME:TYPE}` in the value);
                   its `result_minimums` {NAME: integer m} state `m <= NAME` of a fresh Z binder of those
                   values in the return entry, which the call block proves (call_boundary.call_return_seed)
  call_return      the `return_facts` of the call whose `return_site_pc` is `pc` (role -> `kind`)
  function_return  a `function_returns` row: `return_instruction_pc` and `return_fact` (True without facts)
  access           an `access_placements` row: `pc` and `placement` {`array`, `index`, `scale`, `offset`},
                   which the forward pass reads (symbolic_state.ACCESS_PLACEMENTS)
  frame            the saved frame where an entry forgets it: `slots` [{`offset` (bytes from the entry
                   stack pointer, negative), `coq` (the value the slot holds)}] and `sites` [pc]. A call
                   return site gets one fact per slot, `<binder> = (<coq>)`, on the binder of that unknown
                   slot cell (`entry_hist.slot_binder_name`, profile `frame_slots`), as `return_facts` of
                   the call whose `return_site_pc` it is. Any other site is a join: `join_frames[pc]` lists
                   the slots, and its seed holds each slot's value as a store at the slot's prologue
                   address (entry_hist.frame_writes), so the paths after it load the value itself; each
                   edge into a site proves the value of the cell it holds
  potential        (boundary `loop_cut`) a row {`at`, `potential`: Coq Z text over the cut's binders,
                   `entry_bound`?: Coq Z text over `args`, `returnAddress`} adds `potentials[pc]`
                   {`potential`, `binders`, `entry_bound`?} (tools/block/budgets.py). The cut must exist
                   (a loop_cut row or a `loop_heads` entry at `pc`); every binder the text names is a
                   binder of that cut, and it names at least one. A row with `potential` and binders or
                   facts is also the cut's loop_cut row.
The profile key `charged: true` (copied from the profile part) needs `charged_code` {`module`,
`premise`}: the charged selected code (`instr_lookup_resources_charged ...`) that replaces
`selected_code` as every block's code premise. A charged function's entries own `step_budget (B)`
with B from budgets.py. A back edge adds no obligation of its own: the block before the back edge
enters with its budget over the loop body's binders, and its step into the cut must establish
`step_budget (<potential at the next iteration>)`, the cut's entry; the inequality between the two
potentials is left to that block's proof.
The compiled profile carries `generated_from` {`path`, `sha256`}. The three hand-written profiles have
no annotation file.

`test` instantiates each row's binders from the snapshots `RUN/exec/<input>/STATE-<oooo>.json` at its pc
(schema `oblig-exec-snapshot/1`): a binder with a `register` takes that register at the visit; a binder
with `exec` (a typed ghost binder too) takes that Coq term. In facts and `exec` terms, `{xN}` (or an ABI
name) is the register at the function entry (STATE-0000.json, first visit; for a loop cut at the loop
entry) and `{reg:xN}` the register at the visit; `{entry:xN}` is the register at the function entry for
every row; `{bytes:NAME}` is the snapshot memory range NAME at the visit as a byte list and
`{entry:bytes:NAME}` the range at the function entry; `{memory}` is every range at the visit as
`list (Z * list byte)`, read with `snapshotRead memory address size` (the bytes, `[]` outside every range)
and `snapshotWord memory address` (the little-endian 64-bit word; `snapshotLe bytes` of a byte list).
The file's optional `test` {`imports` [module], `lets` [{`name`, `exec`}]} adds `Require Import` lines and
lets bound before every row's binders (a contract's `args` record from the entry registers). `--coqc-args`
takes a JSON list `[coqc, flag, ...]` (a render's coqc-args.json) whose load paths the imports need.
Each fact is evaluated with `Eval vm_compute in bool_decide (...)`. One false fact rejects the row and names
its input; a fact that does not elaborate (a contract name the snapshot cannot give) is reported unchecked.
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
sys.path.insert(0, str(ROOT / 'tools/block'))
import entry_hist  # noqa: E402
SCHEMA = 'zesu.annotations.v1'
BOUNDARIES = ('entry', 'loop_cut', 'join', 'call_site', 'call_return', 'function_return', 'access', 'frame')
GENERATED_KEYS = ('loop_designs', 'join_designs', 'calls', 'function_returns', 'access_placements',
                  'domain_component', 'opaque_predicates', 'unreachable_entries', 'unreachable_reached',
                  'join_drops', 'generated_from', 'potentials')
POTENTIAL_KEYS = {'id', 'request', 'at', 'potential', 'entry_bound', 'author'}
REGISTER_BINDER = re.compile(r'(?:machine|call|loop)_x\d+')
IDENTIFIER = re.compile(r"(?<![\w'.])[A-Za-z_][\w']*(?![\w'.])")
OPAQUE_USES = ('framed', 'consumed', 'produced')
PC = re.compile(r'(?:[^+\s]+)?\+0x[0-9a-f]+')
ABI = ['zero', 'ra', 'sp', 'gp', 'tp', 't0', 't1', 't2', 's0', 's1', 'a0', 'a1', 'a2', 'a3', 'a4', 'a5', 'a6',
       'a7', 's2', 's3', 's4', 's5', 's6', 's7', 's8', 's9', 's10', 's11', 't3', 't4', 't5', 't6']
HEADER = ('From stdpp Require Import bitvector.definitions decidable.\n'
          'From Coq Require Import ZArith List.\nImport ListNotations.\nLocal Open Scope Z_scope.\n')
# The snapshot readers of `{memory}` (see the module text).
READERS = ('Fixpoint snapshotLe (bytes : list (bv 8)) : Z :=\n'
           '  match bytes with [] => 0 | b :: rest => bv_unsigned b + 256 * snapshotLe rest end.\n'
           'Definition snapshotRead (memory : list (Z * list (bv 8))) (address size : Z) : list (bv 8) :=\n'
           '  match List.find (fun range => (fst range <=? address) &&\n'
           '      (address + size <=? fst range + Z.of_nat (List.length (snd range)))) memory with\n'
           '  | Some range => List.firstn (Z.to_nat size) (List.skipn (Z.to_nat (address - fst range)) (snd range))\n'
           '  | None => [] end.\n'
           'Definition snapshotWord (memory : list (Z * list (bv 8))) (address : Z) : Z :=\n'
           '  snapshotLe (snapshotRead memory address 8).\n')


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
    setup = data.get('test', {})
    if (not isinstance(setup, dict) or set(setup) - {'imports', 'lets'}
            or not all(isinstance(module, str) and re.fullmatch(r'[\w.]+', module) for module in setup.get('imports', []))
            or not all(isinstance(item, dict) and set(item) == {'name', 'exec'} and isinstance(item['exec'], str)
                       and re.fullmatch(r"[A-Za-z_][\w']*", str(item['name'])) for item in setup.get('lets', []))):
        raise AnnotationError('`test` is {imports: [module], lets: [{name, exec}]}')
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
    """The shape of a call row's `opaque`, `returns` and `result_words` rows (call_boundary consumes them)."""
    for item in row['call'].get('opaque', []):
        if not isinstance(item.get('spec'), str) or item.get('use') not in OPAQUE_USES:
            raise AnnotationError('%s: an opaque row has `spec` and a `use` among %s'
                                  % (row['id'], ', '.join(OPAQUE_USES)))
        callers = item.get('caller', [])
        if item['use'] == 'consumed' and not callers or item['use'] == 'produced' and callers \
                or not all(isinstance(text, str) for text in callers):
            raise AnnotationError('%s: a consumed opaque row names its caller resources, a produced one none'
                                  % row['id'])
        pieces = item.get('as')
        if pieces is not None and (item['use'] != 'produced' or not isinstance(pieces, list) or not pieces
                                   or not all(isinstance(piece, str) or isinstance(piece, dict)
                                              and set(piece) == {'coq', 'length'} for piece in pieces)):
            raise AnnotationError('%s: `as` belongs to a produced opaque row: its pieces are texts or {coq, length}'
                                  % row['id'])
    for item in row['call'].get('returns', []):
        if not isinstance(item.get('index'), int) or not re.fullmatch(r'x(1[0-7])', str(item.get('register'))):
            raise AnnotationError('%s: a returns row has an integer `index` and an argument register' % row['id'])
    words = row['call'].get('result_words', {})
    if not isinstance(words, dict) or not all(re.fullmatch(r'[0-9]+', str(key)) and isinstance(value, str)
                                              for key, value in words.items()):
        raise AnnotationError('%s: result_words maps byte offsets to value texts' % row['id'])
    minimums = row['call'].get('result_minimums', {})
    fresh = {name for value in words.values() for name, kind in re.findall(r'\{fresh:(\w+):([^{}]+)\}', value)
             if ' '.join(kind.split()) == 'Z'}
    if not isinstance(minimums, dict) or not all(name in fresh and type(value) is int
                                                 for name, value in minimums.items()):
        raise AnnotationError('%s: result_minimums maps fresh Z binders of result_words to integers' % row['id'])


def compile_profile(data, source=None):
    """The function profile of an annotation file (see the module text)."""
    validate(data)
    profile = json.loads(json.dumps(data['profile']))
    profile.setdefault('function', data['function'])
    profile.setdefault('symbol', data['symbol'])
    heads = list(profile.get('loop_heads', []))
    loop_designs, join_designs, calls, returns, placements = [], {}, [], [], []
    unreachable, reached_pcs, drops = [], [], {}
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
        elif boundary == 'loop_cut' and set(row) <= POTENTIAL_KEYS:
            continue   # a potential row alone: compiled after every cut is known (_potentials)
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
            loose = [binder for binder in row.get('binders', [])
                     if not binder.get('register') and binder.get('role') != 'index']
            if any(not isinstance(binder.get('type'), str) or not binder['type'] for binder in loose):
                raise AnnotationError('%s: a loop-cut binder without a register has a `type`' % row['id'])
            if row.get('resources') or row.get('replaces') or loose:
                for item in row.get('resources', []):
                    if not (isinstance(item, str) or isinstance(item, dict) and set(item) == {'coq', 'length'}):
                        raise AnnotationError('%s: a loop-cut resource is a text or {coq, length}' % row['id'])
                for item in row.get('replaces', []):
                    if not (isinstance(item, str) or isinstance(item, dict) and set(item) == {'id'}):
                        raise AnnotationError('%s: a replaced loop-entry component is a text or {id}' % row['id'])
                design['owned'] = {'binders': [{'name': binder['name'], 'type': binder['type']} for binder in loose],
                                   'resources': list(row.get('resources', [])),
                                   'replaces': list(row.get('replaces', []))}
            loop_designs.append(design)
        elif boundary == 'join':
            roles = {fact['role'] for fact in facts}
            if 'unreachable' in roles:
                # No path reaches the block: the renderer emits ⌜False⌝ as its entry (and refuses the row
                # where the forward pass finds a path, unless the row says the path's guards contradict).
                reached = row.get('reached')
                if reached not in (None, 'contradictory_guards'):
                    raise AnnotationError('%s: `reached` is contradictory_guards' % row['id'])
                effective = [fact for fact in facts if fact['role'] != 'relies_on' or reached is None]
                if {fact['role'] for fact in effective} != {'unreachable'} \
                        or [fact['coq'] for fact in effective] != ['False'] or row.get('drop'):
                    raise AnnotationError('%s: an unreachable row has the single fact False' % row['id'])
                unreachable.append(at['pc'])
                if reached:
                    reached_pcs.append(at['pc'])
                continue
            for item in row.get('drop', []):
                if set(item) != {'root', 'resources'} or not item['resources'] \
                        or not all(isinstance(text, str) for text in item['resources']):
                    raise AnnotationError('%s: a drop row has `root` and its resource texts' % row['id'])
                drops.setdefault(at['pc'], []).append(dict(item))
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
        elif boundary == 'frame':
            slots, sites = row.get('slots') or [], row.get('sites') or []
            if not slots or not sites or row.get('facts') \
                    or not all(isinstance(pc, str) and PC.fullmatch(pc) for pc in sites) \
                    or any(set(slot) != {'offset', 'coq'} or not isinstance(slot['offset'], int)
                           or slot['offset'] % 8 or not isinstance(slot['coq'], str) for slot in slots) \
                    or len({slot['offset'] for slot in slots}) != len(slots):
                raise AnnotationError('%s: a frame row has `slots` [{offset (a multiple of 8), coq}] with '
                                      'distinct offsets, `sites` [pc] and no facts' % row['id'])
            if not profile.get('frame_slots'):
                raise AnnotationError('%s: a frame row needs the profile key frame_slots' % row['id'])
    join_frames = {}
    for row in rows:
        if row['at']['boundary'] == 'frame':
            for pc in row['sites']:
                owners = [call for call in calls if call.get('return_site_pc') == pc]
                for call in owners:
                    call.setdefault('return_facts', []).extend(
                        {'kind': 'fact', 'coq': '%s = (%s)' % (entry_hist.slot_binder_name(slot['offset']), slot['coq'])}
                        for slot in row['slots'])
                if not owners:
                    join_frames.setdefault(pc, []).extend(dict(slot) for slot in row['slots'])
        if row['at']['boundary'] != 'call_return':
            continue
        owners = [call for call in calls if call.get('return_site_pc') == row['at']['pc']]
        if len(owners) != 1:
            raise AnnotationError('%s: no single call_site row returns to %s' % (row['id'], row['at']['pc']))
        owners[0].setdefault('return_facts', []).extend(_kind_fact(fact) for fact in row.get('facts', []))
    if heads:
        profile['loop_heads'] = heads
    for key, value in (('loop_designs', loop_designs), ('join_designs', join_designs), ('calls', calls),
                       ('function_returns', returns), ('access_placements', placements),
                       ('unreachable_entries', unreachable), ('unreachable_reached', reached_pcs),
                       ('join_drops', drops), ('join_frames', join_frames),
                       ('potentials', _potentials(rows, heads))):
        if value:
            profile[key] = value
    _check_charged(profile)
    if source is not None:
        profile['generated_from'] = {'path': str(Path(source).resolve().relative_to(ROOT)),
                                     'sha256': hashlib.sha256(Path(source).read_bytes()).hexdigest()}
    return profile


def _potentials(rows, heads):
    """{pc: {potential, binders, entry_bound?}} of the rows with `potential` (see the module text)."""
    cut_binders = {}
    for row in rows:
        if row['at']['boundary'] == 'loop_cut' and not set(row) <= POTENTIAL_KEYS:
            cut_binders.setdefault(row['at']['pc'], []).extend(
                binder['name'] for binder in row.get('binders', []) if binder['name'] not in
                cut_binders.get(row['at']['pc'], []))
    every = {name for names in cut_binders.values() for name in names}
    potentials = {}
    for row in rows:
        if 'potential' not in row:
            continue
        pc, text = row['at']['pc'], row['potential']
        if row['at']['boundary'] != 'loop_cut':
            raise AnnotationError('%s: a potential row is at a loop_cut' % row['id'])
        if pc not in heads:
            raise AnnotationError('%s: no loop cut exists at %s' % (row['id'], pc))
        if pc in potentials:
            raise AnnotationError('%s: a second potential row at %s' % (row['id'], pc))
        if not isinstance(text, str) or not text.strip() or 'entry_bound' in row and not (
                isinstance(row['entry_bound'], str) and row['entry_bound'].strip()):
            raise AnnotationError('%s: potential and entry_bound are Coq Z texts' % row['id'])
        own = cut_binders.get(pc, [])
        names = set(IDENTIFIER.findall(text))
        unknown = sorted(name for name in names if name not in own
                         and (name in every or REGISTER_BINDER.fullmatch(name)))
        if unknown:
            raise AnnotationError('%s: the potential names binders that the cut at %s does not bind: %s'
                                  % (row['id'], pc, ', '.join(unknown)))
        if not names & set(own):
            raise AnnotationError('%s: the potential names none of the binders of the cut at %s'
                                  % (row['id'], pc))
        if '{' in text:
            raise AnnotationError('%s: a potential is over the cut\'s binders, without placeholders' % row['id'])
        bound = row.get('entry_bound')
        if bound is not None and set(IDENTIFIER.findall(bound)) & set(own):
            raise AnnotationError('%s: an entry_bound is over args and returnAddress, not the cut\'s binders'
                                  % row['id'])
        potentials[pc] = {'potential': text, 'binders': list(own),
                          **({'entry_bound': bound} if bound is not None else {})}
    return potentials


def _check_charged(profile):
    """`charged` is true or absent; a charged profile names its charged selected code."""
    if 'charged' not in profile:
        return
    code = profile.get('charged_code')
    if profile['charged'] is not True or not isinstance(code, dict) or set(code) != {'module', 'premise'}:
        raise AnnotationError('the profile key charged is true and needs charged_code {module, premise}')


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
    # Z literals mapped to bytes: a `BV 8 n` literal elaborates a proof per byte (minutes on a 576-byte frame).
    data = bytes.fromhex(row['hex'])
    return '(List.map (Z_to_bv 8) [' + '; '.join('%d' % byte for byte in data) + '])'


def memory_list(memory):
    """`{memory}`: every snapshot range as a Coq `list (Z * list byte)`."""
    return '[' + '; '.join('(%d, %s)' % (row['base'], byte_list(row)) for row in memory) + ']'


def substitute(text, entry, regs, memory, start=None):
    """`start`: the function-entry visit ({regs, memory}) of `{entry:...}` (the module text)."""
    def replace(match):
        token = match[1]
        if token == 'memory':
            return 'snapshotMemory'
        scope_regs, scope_memory = regs, memory
        if token.startswith('entry:'):
            if start is None:
                raise KeyError('no function-entry snapshot for ' + token)
            token, scope_regs, scope_memory = token[6:], start['regs'], start.get('memory', [])
            if not token.startswith('bytes:'):
                return bv(scope_regs[register_key(token)])
        if token.startswith('reg:'):
            return bv(scope_regs[register_key(token[4:])])
        if token.startswith('bytes:'):
            rows = [row for row in scope_memory if row['name'] == token[6:]]
            if len(rows) != 1:
                raise KeyError('no memory range ' + token[6:])
            return byte_list(rows[0])
        return bv(entry[register_key(token)])
    return re.sub(r'\{((?:entry:)?(?:reg:|bytes:)?[\w#.-]+)\}', replace, text)


def fact_term(row, fact, entry, visit, start=None, lets=()):
    """The closed Coq term `let <file lets> <binders> in bool_decide (<fact>)` of one visit."""
    regs, memory = visit['regs'], visit.get('memory', [])
    texts = [*(item['exec'] for item in lets), *(binder.get('exec', '') for binder in row.get('binders', [])),
             fact['coq']]
    bound = ['let snapshotMemory := %s in' % memory_list(memory)] if any('{memory}' in text for text in texts) else []
    for item in lets:
        bound.append('let %s := %s in' % (item['name'], substitute(item['exec'], entry, regs, memory, start)))
    for binder in row.get('binders', []):
        if binder.get('register'):
            bound.append('let %s := %s in' % (binder['name'], bv(regs[register_key(binder['register'])])))
        elif binder.get('exec'):
            bound.append('let %s := %s in' % (binder['name'], substitute(binder['exec'], entry, regs, memory, start)))
    return ' '.join(bound + ['bool_decide (%s)' % substitute(fact['coq'], entry, regs, memory, start)])


def evaluate(terms, coqc, directory, split=True, imports=()):
    """[True | False | error text] per term: one coqc run, then (with `split`) one per term after an
    error; without `split`, None after an error. `coqc` is a command list (coqc and its flags)."""
    prefix = HEADER + ''.join('Require Import %s.\n' % module for module in imports) + READERS

    def run(batch, name):
        path = Path(directory) / name
        path.write_text(prefix + ''.join('Eval vm_compute in (%s).\n' % term for term in batch))
        result = subprocess.run([*coqc, path.name], cwd=directory, capture_output=True, text=True)
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
    """[(input id, entry registers, visit, function-entry visit | None)] at the row's pc, over every
    input dir of RUN/exec.

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
        entry = directory / 'STATE-0000.json'
        start = json.loads(entry.read_text())['visits'][0] if entry.exists() else None
        if loop:
            predecessor = directory / ('STATE-%s.json' % offset_key(at['predecessor'])) \
                if at.get('predecessor') else None
            marks = sorted(visit.get('insn', 0) for visit in json.loads(predecessor.read_text())['visits']) \
                if predecessor is not None and predecessor.exists() else []
            for visit in visits:
                before = [mark for mark in marks if mark < visit.get('insn', 0)]
                head = next(other for other in visits if other.get('insn', 0) > before[-1]) if before else visits[0]
                found.append((data.get('input', directory.name), head['regs'], visit, start))
            continue
        if start is None:
            continue
        for visit in visits:
            found.append((data.get('input', directory.name), start['regs'], visit, start))
    return found


def test_rows(data, run, row_ids=None, coqc=None):
    """{'verdict': 'passed' | 'rejected' | 'untested', ...} over the selected rows. `coqc`: a command list."""
    validate(data)
    coqc = coqc or ([coqc_command()] if coqc_command() else None)
    if coqc is None:
        raise SystemExit('annotations test: no coqc (set COQC or ISLARIS_REPO)')
    setup = data.get('test', {})
    imports, lets = setup.get('imports', []), setup.get('lets', [])
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
                return [fact_term(row, fact, entry, visit, start, lets)
                        for _, entry, visit, start in visits for fact in facts]
            values = evaluate(terms_of(facts), coqc, directory, split=False, imports=imports)
            if values is None:
                # A fact that does not elaborate on the first visit stays unchecked on every visit.
                _, entry, visit, start = visits[0]
                first = evaluate([fact_term(row, fact, entry, visit, start, lets) for fact in facts], coqc, directory,
                                 imports=imports)
                for fact, value in zip(list(facts), first):
                    if not isinstance(value, bool):
                        unchecked.append({'row': row['id'], 'fact': fact['coq'], 'error': value})
                        facts.remove(fact)
                values = evaluate(terms_of(facts), coqc, directory, imports=imports) if facts else []
            # Visit order, then fact order: the first false fact names the input, its visit and the fact.
            for index, value in enumerate(values):
                (input_id, _, visit, _), fact = visits[index // len(facts)], facts[index % len(facts)]
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
    test_parser.add_argument('--coqc-args', type=Path,
                             help='JSON list [coqc, flag, ...] (a render coqc-args.json) for the file\'s test imports')
    options = parser.parse_args()
    if options.command == 'compile':
        return cmd_compile(options.function)
    if options.command == 'check':
        return cmd_check(options.function)
    source = options.annotations or annotation_path(options.function)
    coqc = json.loads(options.coqc_args.read_text()) if options.coqc_args else None
    result = test_rows(json.loads(source.read_text()), options.run, options.row, coqc)
    print(json.dumps(result, indent=1))
    return 1 if result['verdict'] == 'rejected' else 0


if __name__ == '__main__':
    sys.exit(main())
