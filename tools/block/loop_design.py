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
from join_generalize import check_fact_accounting
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


def class_components(order, sources, changed, path_conditions, names):
    """(owned, pure, conditions, accounting) of a loop class from its entry edge: the owned
    resources (a changed register holds its binder), the pure resource facts, and the path
    conditions over class names (`names`, and the arguments).

    Every pure fact of the entry edge (a join's ⌜True⌝ placeholder is accounted by that join) and
    every path condition is a class fact or a drop under a named rule (`trace_local_witness`: no
    Coq text; `outside_class_scope:<names>`: it names values the class does not bind);
    join_generalize.check_fact_accounting raises on a silent loss."""
    owned, pure, components, dropped = [], [], [], []
    for key in order:
        text = sources[key]
        register = re.match(r'"(x\d+)" ↦ᵣ', text)
        if register and register[1] in changed:
            owned.append('"%s" ↦ᵣ RVal_Bits (%s : bv 64%%N)' % (register[1], changed[register[1]]))
        elif text == 'True':
            continue
        elif text.startswith('⌜'):
            pure.append(text)
            components.append({'id': key, 'source': text})
        else:
            owned.append(text)
    conditions = []
    for position, condition in enumerate(path_conditions):
        key = 'path_condition:%d' % position
        try:
            text = condition.coq()
        except ValueError:
            dropped.append({'component': key, 'rule': 'trace_local_witness'})
            continue
        outside = sorted(name for name in _inputs(condition) if name not in names and 'args' not in name)
        if outside:
            dropped.append({'component': key, 'rule': 'outside_class_scope:' + ','.join(outside)})
            continue
        conditions.append('⌜(%s) = true⌝' % text)
        components.append({'id': key, 'source': conditions[-1]})
    accounting = check_fact_accounting(
        [key for key in order if sources[key].startswith('⌜') and sources[key] != '⌜True⌝']
        + ['path_condition:%d' % position for position in range(len(path_conditions))],
        components, {'dropped_facts': dropped})
    return owned, pure, conditions, accounting


def _normal(text):
    return ' '.join(str(text).split())


def owned_text(row):
    """The Iris text of one `owned.resources` row: a string, or {coq, length} for a `↦ₘ∗` array."""
    return row['coq'] if isinstance(row, dict) else row


def replaced_components(owned, sources):
    """The component ids of the loop-entry state that the design's `owned.replaces` rows name: an exact
    component text, or {"id": component id}; each names exactly one component, else the design is
    refused."""
    by_text = {}
    for key, text in sources.items():
        by_text.setdefault(_normal(text), []).append(key)
    ids = []
    for item in owned.get('replaces', []):
        keys = ([item['id']] if item['id'] in sources else []) if isinstance(item, dict) \
            else by_text.get(_normal(item), [])
        if len(keys) != 1:
            raise ValueError('The loop design replaces a resource that is not one component of the '
                             'loop-entry state: ' + str(item))
        ids.append(keys[0])
    return ids


def _entry_edges(report, design, profile):
    """The loop-entry edges of a design's head in the forward report (none when it is not reached)."""
    head = profile.pc(design['head'])
    boundary = next((row for row in report['boundaries'] if row['pc'] == head), None)
    return [row for row in (boundary or {}).get('alternatives', [])
            if row['predecessor_pc'] == profile.pc(design['entry_predecessor'])]


def owned_node(row, index, prefix='loop_owned_'):
    """The public seed node of one `owned.resources` row (call_boundary's node kinds)."""
    text = owned_text(row)
    points = re.fullmatch(r'(.+?)\s+(↦ₘ∗|↦ₘ\?)\s+(.+)', text, re.S)
    key = prefix + str(index)
    if points is None:
        return {'kind': 'opaque', 'id': key, 'coq': text}
    from forward_resources import _strip_enclosure
    address = _strip_enclosure(points[1].strip())
    if points[2] == '↦ₘ?':
        return {'kind': 'uninitialized_memory', 'id': key, 'original_component': text, 'address_z': address,
                'length_original_coq': _strip_enclosure(points[3].strip())}
    if not isinstance(row, dict) or 'length' not in row:
        raise ValueError('An owned `↦ₘ∗` resource of a loop design states its length: ' + text)
    from symbolic_state import input_expr
    return {'kind': 'byte_array', 'id': key, 'original_component': text, 'address_z': address,
            'byte_array_expr': input_expr(_strip_enclosure(points[3].strip()), None).to_dict(),
            'element_bits': 8, 'length_original_coq': str(row['length'])}


def owned_seed(seed, design, head, vocabulary):
    """The loop-head seed with the design's owned state (`owned`): the components it `replaces` leave,
    its `resources` and its binders join, and each design fact that names an owned binder (and no
    entry register `{xN}`) is carried as a pure component, so the blocks after the head keep it."""
    from resource_seed import seed_owned_resources
    from symbolic_state import input_expr
    owned = design['owned']
    sources = {component['id']: str(component['seed_component'].get(
        'original_component', component['seed_component'].get('coq', ''))) for component in seed.ownership['components']}
    removed = set(replaced_components(owned, sources))
    nodes = [{**component['seed_component'], 'id': component['id']} for component in seed.ownership['components']
             if component['id'] not in removed]
    # A pure fact keeps the text the join gave it (a fact of a binder the join dropped is in its hidden
    # history group or `⌜True⌝`), not its text in the root seed.
    texts = {component['id']: component.get('source') for component in seed.ownership['components']}
    for node in nodes:
        text = texts.get(node['id'])
        if (node.get('kind') == 'opaque' and str(node.get('coq', '')).startswith('⌜')
                and isinstance(text, str) and text.startswith('⌜') and text != node['coq']):
            node['coq'] = text
            if 'original_component' in node:
                node['original_component'] = text
    # Before the closing component (`True`, or the continuation `K` of a seed that carries it).
    terminal = next((index for index, node in enumerate(nodes) if node.get('coq') in ('True', 'K')), len(nodes))
    names = {row['name'] for row in owned.get('binders', [])}
    # A loop nested in a loop-owned one keeps the outer loop's ids: its own carry the head.
    prefix = ('loop_owned_%x_' % head if any(str(node['id']).startswith('loop_owned_') for node in nodes)
              else 'loop_owned_')
    carried = [{'kind': 'opaque', 'id': prefix + 'fact_%d' % index, 'coq': '⌜' + row['coq'] + '⌝'}
               for index, row in enumerate(design.get('facts', []))
               if _words(row['coq']) & names and '{x' not in row['coq']]
    nodes[terminal:terminal] = [owned_node(row, index, prefix) for index, row in enumerate(owned['resources'])] + carried
    binders = [{key: value for key, value in binder.items() if key != 'scope'} for binder in seed.ownership['binders']]
    # `owned`: a ghost binder of the loop's owned state; a join or loop head below keeps it (drop_unheld_binders).
    binders += [{'name': row['name'], 'type': row['type'], 'expression': input_expr(row['name'], None).to_dict(),
                 'owned': True} for row in owned.get('binders', [])]
    # A register's witness that no binder row expresses (a binder of an earlier seed the join kept by name)
    # gets one; the registers themselves are the loop-head state's (below).
    named = {binder['name'] for binder in binders if 'expression' in binder}
    for node in nodes:
        witness = node.get('symbolic_witness')
        if node.get('kind') == 'register' and witness and witness not in named:
            binders.append({'name': witness, 'type': 'bv 64', 'expression': input_expr(witness, 64).to_dict()})
            named.add(witness)
    public = {'schema': 'h1-public-entry-seed.v1', 'function': design.get('function'), 'entry_pc': hex(head),
              'assertion_tree': {'kind': 'exists', 'binders': binders, 'components': nodes},
              'source_bindings': list(seed.ownership.get('provenance', {}).get('source_bindings', []))}
    public['_input_sha256'] = hashlib.sha256(json.dumps(public, sort_keys=True).encode()).hexdigest()
    facts = [fact for fact in seed.facts
             if fact['kind'] not in ('permission', 'nonwrap') and not fact['fact_id'].endswith(':separation')
             and not {fact.get('terms', {}).get(field) for field in ('left', 'right', 'resource_id')} & removed]
    rebuilt = seed_owned_resources(public, entry_pc=head, vocabulary=vocabulary, facts=facts)
    rebuilt.state.registers.update(seed.state.registers)
    rebuilt.state.retained_registers = dict(rebuilt.state.registers)
    rebuilt.state.conditions = list(seed.state.conditions)
    known = {region.ownership_id: region for region in seed.state.memory}
    rebuilt.state.memory = [known.get(region.ownership_id, region) for region in rebuilt.state.memory]
    rebuilt.state.word_links = [dict(link) for link in seed.state.word_links if link['resource_id'] not in removed]
    rebuilt.join_kind = 'loop_head'
    return rebuilt


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
    inherited = [(binder['name'], binder['type']) for binder in scope['binders']]
    names = {name for name, _ in inherited} | set(changed.values()) | {design['index']}
    owned_design = design.get('owned')
    if owned_design:
        order = [key for key in order if key not in replaced_components(owned_design, sources)]
    owned, pure, conditions, _ = class_components(order, sources, changed, state.conditions, names)
    if owned_design:
        owned += [owned_text(row) for row in owned_design['resources']]
    if pure.count('⌜domain args⌝') != 1:
        raise ValueError('The loop-entry state has no single domain component.')
    facts = []
    for row in design['facts']:
        text = re.sub(r'\{(x\d+)\}', lambda match: '(' + entry_values[match[1]] + ')', row['coq'])
        facts.append('⌜' + text + '⌝')
    body = ' ∗ '.join(owned + pure + conditions + facts)
    used = _words(body)
    binders = ['(%s : bv 64)' % name for name in changed.values()]
    binders.append('(%s : lvar "zesuLoopIndex" Z)' % design['index'])
    binders += ['(%s : %s)' % (name, kind) for name, kind in inherited if name in used]
    binders += ['(%s : %s)' % (row['name'], row['type']) for row in (owned_design or {}).get('binders', [])]
    name = 'generatedLoop' + design['head'] + 'Class0'
    source = ('Definition ' + name + profile.telescope() + ' (domain : ' + profile.args_type + ' -> Prop)'
              ' : iProp Sigma :=\n  ((∃ ' + ' '.join(binders) + ', (' + body + ')))%I.')
    record = {'entry_edge': entry['predecessor_pc'], 'changed_registers': changed,
              'resource_facts': len(pure), 'path_conditions': len(conditions),
              'design_facts': [{'kind': row['kind'], 'coq': row['coq']} for row in design['facts']],
              **({'owned': owned_design} if owned_design else {})}
    return source, record


def reseat_orphaned(registers, entry_registers, design_registers, taken):
    """Give a fresh binder to each register that names a binder no register holds any more.

    Overwriting a design register with its loop binder leaves the binder it held at the
    loop entry without a holder. Another register that names that binder gets a fresh
    seed binder; the loop class keeps its exact entry value. Returns the new binder rows."""
    from symbolic_state import input_expr
    holders = [value.value for value in registers.values() if value.op == 'input']
    orphaned = {value.value for register, value in entry_registers.items()
                if register in design_registers and value.op == 'input' and value.value not in holders}
    taken, added = set(taken), []
    for register in sorted(registers, key=lambda key: (len(key), key)):
        value = registers[register]
        if register in design_registers or not GPR.fullmatch(register) or not orphaned & set(_inputs(value)):
            continue
        index = 1
        while 'machine_%s_%d' % (register, index) in taken:
            index += 1
        fresh = input_expr('machine_%s_%d' % (register, index), value.width)
        taken.add(fresh.value)
        added.append({'name': fresh.value, 'type': 'bv %d' % value.width, 'expression': fresh.to_dict()})
        registers[register] = fresh
    return added


def cursor_stride(design, register):
    """The constant a cursor register advances by per iteration, from its index link (1 without
    a coefficient)."""
    for row in design.get('facts', []):
        if row['kind'] != 'index_link' or '{' + register + '}' not in row['coq']:
            continue
        match = re.search(r'\{' + register + r'\} [+-] (?:(\d+) \* )?' + re.escape(design['index']) + r'\)', row['coq'])
        if match:
            return int(match[1] or 1)
    return 1


def cursor_extent(design, cursor, function):
    """The bytes the cursor covers: the design's `width`, else the widest access at the cursor in
    the loop body (loop_structure.cursor_width), 1 without the function's rows."""
    if 'width' in cursor:
        return int(cursor['width'])
    if function is None:
        return 1
    from loop_structure import cursor_width
    stride = int(cursor['stride']) if 'stride' in cursor else cursor_stride(design, cursor['register'])
    return cursor_width(function, design['_head'], cursor['register'], stride)


def cursor_owner(seed, cursor, entry_value):
    """The owned resource a cursor indexes: the one named by the design's `array`, or for an
    inferred cursor (`array` null) the one owned byte array whose base is an addend of the
    register's entry value."""
    if cursor['array'] is not None:
        # The array keeps its contract name in the seed component when a join packaged it.
        return next(resource for resource in seed.resources if resource.id in
                    {row['id'] for row in seed.ownership['components']
                     if cursor['array'] in (row.get('value'), (row.get('seed_component') or {})
                                            .get('byte_array_expr', {}).get('value'))})
    from symbolic_state import _addends
    terms, _ = _addends(entry_value)
    owners = [resource for resource in seed.resources if getattr(resource, 'byte_array', None) is not None
              and _addends(resource.base)[0] and all(term in terms for term in _addends(resource.base)[0])]
    if len(owners) != 1:
        raise ValueError('The cursor %s (entry value %s) names %d owned arrays; its design must name the array'
                         % (cursor['register'], entry_value.coq() if hasattr(entry_value, 'coq') else entry_value,
                            len(owners)))
    return owners[0]


def loop_head_seed(report, design, profile, *, root_seed, vocabulary, continuation, live_registers=None,
                   function=None):
    """Return a forward-pass seed at the loop head from its entry edge and design.

    The seed keeps the entry edge's resources and path conditions. Each changed
    register becomes its binder. A changed register that the design links to
    an owned array by an index fact (`array_cursor`, one row or a list) keeps
    that array's base as an addend, so the body reads or stores the array at a
    symbolic index; its index range stays an open obligation. The cursor covers the bytes one
    iteration accesses at it (cursor_extent: an 8-byte load at a byte-array cursor with stride 8
    covers 8 bytes). The class row, not this seed, states the
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
    entry_registers = dict(seed.state.registers)
    cursors = design.get('array_cursor') or []
    cursors = cursors if isinstance(cursors, list) else [cursors]
    design = {**design, '_head': int(head, 0)}
    added = []
    for register, binder in design['registers'].items():
        value = input_expr(binder, 64)
        cursor = next((row for row in cursors if row['register'] == register), None)
        if cursor:
            owner = cursor_owner(seed, cursor, entry_registers.get(register))
            offset = input_expr(binder + '_offset', 64)
            value = operation('bvadd', owner.base, offset)
            added.append({'name': binder + '_offset', 'type': 'bv 64', 'expression': offset.to_dict()})
            seed.facts.append({'fact_id': owner.id + ':loop-cursor-extent', 'kind': 'bounds',
                               'status': 'derived-by-pass',
                               'terms': {'resource_id': owner.id, 'index': 0,
                                         'count': cursor_extent(design, cursor, function),
                                         'coq_statement': cursor['extent_reason']},
                               'origin': {'loop_design': design['head'], 'facts': cursor['extent_reason']}})
        else:
            added.append({'name': binder, 'type': 'bv 64', 'expression': value.to_dict()})
        seed.state.registers[register] = value
    added += reseat_orphaned(seed.state.registers, entry_registers, design['registers'],
                             {row['name'] for row in [*seed.ownership['binders'], *added]})
    seed.state.retained_registers = dict(seed.state.registers)
    tree = seed.ownership['tree']['left']
    tree['binders'] = [*tree['binders'], *({k: v for k, v in row.items()} for row in added)]
    seed.ownership['binders'] = [*seed.ownership['binders'], *({**row, 'scope': [0]} for row in added)]
    seed.join_kind = 'loop_head'
    if design.get('owned'):
        return owned_seed(seed, design, int(head, 0), vocabulary)
    return seed


def inferred_designs(report_path):
    """The inferred designs run_source_pass.py wrote beside FORWARD.json (loop_infer.py)."""
    path = Path(report_path).parent / 'LOOP-DESIGNS.json'
    return json.loads(path.read_text())['designs'] if path.exists() else []


def loop_head_rows(report, report_path, profile):
    rows, refusals = [], {}
    for design in [*profile.get('loop_designs', []), *inferred_designs(report_path)]:
        try:
            source, record = loop_class(report, design, profile)
        except (ValueError, StopIteration) as error:
            if not design.get('inferred') and _entry_edges(report, design, profile):
                raise
            # A design whose head the pass did not seed (no entry edge reaches it: an earlier stop) has
            # no class; its head stays a refused cut (the forward pass's reaching stops say why).
            refusals[design['head']] = str(error) or 'the loop head has no boundary'
            continue
        rows.append({'block': design['head'], 'source': _bind(profile.path), 'verification': _bind(report_path),
                     'classes': [source], 'domain': 'domain', 'domain_component': profile['domain_component'],
                     'continuation': 'K', 'design': record})
    return {'schema': 'fp301-authenticated-loop-heads-v1', 'rows': rows,
            **({'inferred_refusals': refusals} if refusals else {})}


if __name__ == '__main__':
    import argparse, sys
    sys.path.insert(0, str(Path(__file__).resolve().parent))
    from function_profiles import load_profile
    import entry_hist
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--function', required=True)
    parser.add_argument('--forward', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    options = parser.parse_args()
    profile = load_profile(options.function)
    entry_hist.configure(profile)
    rows = loop_head_rows(json.loads(options.forward.read_text()), options.forward, profile)
    options.output.write_text(json.dumps(rows, indent=1, ensure_ascii=False) + '\n')
    print(json.dumps({'rows': len(rows['rows']), 'output': str(options.output)}))
