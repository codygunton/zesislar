"""Render a loop-head class row from a loop design and the loop-entry edge.

The row has the form of the decodeItem loop-head fixture rows
(fixtures/fp301-loop-heads.json): one `generatedLoop<head>Class0` definition
over the loop-entry state. The design row (profile `loop_designs`) names the
registers that the loop body changes, their binders, the loop index, and the
loop facts. The forward pass supplies everything else: the owned resources
of the entry edge, its pure resource facts, and its path conditions that
mention only source terms and class binders. A changed register's value is
replaced by its binder; a design fact refers to an entry value of a register
as {xN}. No proof runs, and the row holds no proof script.
"""
from pathlib import Path
import hashlib
import json
import re

from forward_resource_design import _state_from_result
from symbolic_state import Expr

GPR = re.compile(r'x(?:[0-9]|[12][0-9]|3[01])\Z')


def _bind(path):
    path = Path(path)
    return {'path': str(path), 'sha256': hashlib.sha256(path.read_bytes()).hexdigest()}


def _inputs(value):
    own = [str(value.value)] if value.op == 'input' else []
    return own + [name for child in value.args for name in _inputs(child)]


def _words(text):
    return set(re.findall(r"(?<![\w'.])[A-Za-z_][\w']*", re.sub(r'"[^"]*"', '', text)))


def _define_unheld(state, binders, design, changed, sources):
    """Define each inherited binder that no register holds through a live register.

    A register whose entry value is `b + t` (b once, coefficient 1, t fixed by the edge,
    no wrap under its ranges) determines b = entry - t. For a design register with the
    index link `machine_r = {r} + K * i`, its entry value is `machine_r - K * i`. Each
    definition is substituted in the register values, the path conditions and the owned
    sources. Returns the entry values that the index links name."""
    from join_generalize import _register_definition, substitute
    from symbolic_state import input_expr, operation
    rewritten = {}
    held = {value.value for name, value in state.registers.items() if value.op == 'input' and name not in changed}
    names = [binder['name'] for binder in binders]
    for name in names:
        if name in held:
            continue
        defined = _register_definition(state, name, unheld=[other for other in names if other not in held])
        if defined is None:
            continue
        register, width, rest = defined
        if register not in changed:
            continue   # The register keeps its entry value; a join seed holds it there.
        links = [row['coq'] for row in design['facts'] if row['kind'] == 'index_link'
                 and '{' + register + '}' in row['coq']]
        match = re.fullmatch(r'bv_unsigned (\S+) = \(bv_unsigned \{' + register + r'\} \+ (?:(\d+) \* )?(\w+)\)%Z',
                             links[0]) if len(links) == 1 else None
        if match is None or match[1] != changed[register] or match[3] != design['index']:
            continue
        entry = '(bv_sub %s (Z_to_bv 64 (%s * %s)))' % (changed[register], match[2] or '1', design['index'])
        definition = input_expr('(bv_sub %s (%s))' % (entry, rest.coq()), width)
        mapping = {input_expr(name, width): definition}
        for other, value in list(state.registers.items()):
            if other != register:
                state.registers[other] = substitute(value, mapping)
        state.conditions = [substitute(condition, mapping) for condition in state.conditions]
        pattern = r"(?<![\w'])" + re.escape(name) + r"(?![\w'])"
        for key, text in list(sources.items()):
            register_text = re.match(r'"(x\d+)" ↦ᵣ', text)
            if register_text and register_text[1] in state.registers and re.search(pattern, text):
                sources[key] = '"%s" ↦ᵣ RVal_Bits (%s : bv 64%%N)' % (register_text[1],
                                                                    state.registers[register_text[1]].coq())
            elif re.search(pattern, text):
                sources[key] = re.sub(pattern, lambda _: definition.value, text)
        rewritten[register] = entry
        held.add(name)
    return rewritten


def loop_class(report, design, profile):
    """Return the class definition text and its provenance record."""
    head = profile.pc(design['head'])
    boundary = next(row for row in report['boundaries'] if row['pc'] == head)
    entries = [row for row in boundary['alternatives'] if row['predecessor_pc'] == profile.pc(design['entry_predecessor'])]
    if len(entries) != 1:
        raise ValueError('The loop head needs exactly one entry edge from ' + design['entry_predecessor'])
    entry = entries[0]
    resource = entry['resource_boundary']
    scope = resource.get('tree', {})
    if scope.get('kind') == 'sep' and scope['left'].get('kind') == 'exists':
        scope = scope['left']   # An edge from a join seed: the join's witness scope.
    if resource.get('block_status') != 'completed' or scope.get('kind') != 'exists':
        raise ValueError('The loop-entry edge has no complete owned state.')
    state = _state_from_result(entry['state'])
    values = {**state.retained_registers, **state.registers}
    sources = {row['id']: row['source'] for row in resource['components']}
    order = [child['id'] for child in scope['body']['children']]
    changed = design['registers']
    state.registers = {name: value for name, value in values.items() if GPR.fullmatch(name)}
    rewritten = _define_unheld(state, scope['binders'], design, changed, sources)
    values = state.registers
    entry_values = {name: values[name].coq() for name in values if GPR.fullmatch(name)}
    entry_values.update(rewritten)
    owned, pure = [], []
    for key in order:
        text = sources[key]
        register = re.match(r'"(x\d+)" ↦ᵣ', text)
        if register and register[1] in changed:
            owned.append('"%s" ↦ᵣ RVal_Bits (%s : bv 64%%N)' % (register[1], changed[register[1]]))
        elif text == 'True':
            continue
        elif text.startswith('⌜'):
            pure.append(text)
        else:
            owned.append(text)
    if pure.count('⌜domain args⌝') != 1:
        raise ValueError('The loop-entry state has no single domain component.')
    inherited = [(binder['name'], binder['type']) for binder in scope['binders']]
    names = {name for name, _ in inherited} | set(changed.values()) | {design['index']}
    conditions = []
    for condition in state.conditions:
        try:
            text = condition.coq()
        except ValueError:
            continue  # A trace-local witness fact is not a loop fact.
        if all(name in names or 'args' in name for name in _inputs(condition)):
            conditions.append('⌜(%s) = true⌝' % text)
    facts = []
    for row in design['facts']:
        text = re.sub(r'\{(x\d+)\}', lambda match: '(' + entry_values[match[1]] + ')', row['coq'])
        facts.append('⌜' + text + '⌝')
    body = ' ∗ '.join(owned + pure + conditions + facts)
    used = _words(body)
    binders = ['(%s : bv 64)' % name for name in changed.values()]
    binders.append('(%s : lvar "zesuLoopIndex" Z)' % design['index'])
    binders += ['(%s : %s)' % (name, kind) for name, kind in inherited if name in used]
    name = 'generatedLoop' + design['head'] + 'Class0'
    source = ('Definition ' + name + profile.telescope() + ' (domain : ' + profile.args_type + ' -> Prop)'
              ' : iProp Sigma :=\n  ((∃ ' + ' '.join(binders) + ', (' + body + ')))%I.')
    record = {'entry_edge': entry['predecessor_pc'], 'changed_registers': changed,
              'resource_facts': len(pure), 'path_conditions': len(conditions),
              'design_facts': [{'kind': row['kind'], 'coq': row['coq']} for row in design['facts']]}
    return source, record


def loop_head_seed(report, design, profile, *, root_seed, vocabulary, continuation, live_registers=None):
    """Return a forward-pass seed at the loop head from its entry edge and design.

    The seed keeps the entry edge's resources and path conditions. Each changed
    register becomes its binder. A changed register that the design links to
    an owned array by an index fact (`array_cursor`) keeps that array's base as
    an addend, so the body reads the array at a symbolic index; its index range
    stays an open read obligation. The class row, not this seed, states the
    loop facts; this seed only lets the pass reach the loop exits.
    """
    from join_generalize import generalize_owned_join
    from symbolic_state import input_expr, operation
    head = profile.pc(design['head'])
    boundary = next(row for row in report['boundaries'] if row['pc'] == head)
    entries = [row for row in boundary['alternatives']
               if row['predecessor_pc'] == profile.pc(design['entry_predecessor'])]
    if not entries:
        raise ValueError('The loop head has no entry edge from ' + design['entry_predecessor'])
    # Several entry paths join as at any cut; the changed registers then become binders.
    joined = generalize_owned_join(entries, original_seed=root_seed, entry_pc=int(head, 0), vocabulary=vocabulary,
                                   continuation=continuation, outer_names=['args', 'returnAddress'],
                                   live_registers=live_registers)
    seed = joined['seed']
    cursor = design.get('array_cursor')
    added = []
    for register, binder in design['registers'].items():
        value = input_expr(binder, 64)
        if cursor and cursor['register'] == register:
            owner = next(resource for resource in seed.resources if resource.id in
                         {row['id'] for row in seed.ownership['components']
                          if row.get('value') == cursor['array']})
            offset = input_expr(binder + '_offset', 64)
            value = operation('bvadd', owner.base, offset)
            added.append({'name': binder + '_offset', 'type': 'bv 64', 'expression': offset.to_dict()})
            seed.facts.append({'fact_id': owner.id + ':loop-cursor-extent', 'kind': 'bounds',
                               'status': 'derived-by-pass',
                               'terms': {'resource_id': owner.id, 'index': 0, 'count': 1,
                                         'coq_statement': cursor['extent_reason']},
                               'origin': {'loop_design': design['head'], 'facts': cursor['extent_reason']}})
        else:
            added.append({'name': binder, 'type': 'bv 64', 'expression': value.to_dict()})
        seed.state.registers[register] = value
    seed.state.retained_registers = dict(seed.state.registers)
    tree = seed.ownership['tree']['left']
    tree['binders'] = [*tree['binders'], *({k: v for k, v in row.items()} for row in added)]
    seed.ownership['binders'] = [*seed.ownership['binders'], *({**row, 'scope': [0]} for row in added)]
    seed.join_kind = 'loop_head'
    return seed


def loop_head_rows(report, report_path, profile):
    rows = []
    for design in profile.get('loop_designs', []):
        source, record = loop_class(report, design, profile)
        rows.append({'block': design['head'], 'source': _bind(profile.path), 'verification': _bind(report_path),
                     'classes': [source], 'domain': 'domain', 'domain_component': profile['domain_component'],
                     'continuation': 'K', 'design': record})
    return {'schema': 'fp301-authenticated-loop-heads-v1', 'rows': rows}


if __name__ == '__main__':
    import argparse, sys
    sys.path.insert(0, str(Path(__file__).resolve().parent))
    from function_profiles import load_profile
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--function', required=True)
    parser.add_argument('--forward', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    options = parser.parse_args()
    profile = load_profile(options.function)
    rows = loop_head_rows(json.loads(options.forward.read_text()), options.forward, profile)
    options.output.write_text(json.dumps(rows, indent=1, ensure_ascii=False) + '\n')
    print(json.dumps({'rows': len(rows['rows']), 'output': str(options.output)}))
