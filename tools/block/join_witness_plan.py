"""Lower source-derived join witnesses through existing register-pair inputs."""
from copy import deepcopy

from check_data_only_lemmas import rocq_tokens
from render_support import expression


def _spine(tree, *, inputs):
    rows = []
    if not isinstance(tree, dict):
        raise ValueError('A join witness spine must be a source record')
    while tree.get('kind') == 'pair':
        if set(tree) != {'kind', 'left', 'right'} or not isinstance(tree['left'], dict):
            raise ValueError('A join witness pair has an unsupported shape')
        row = tree['left']
        if inputs and (row.get('kind') != 'register' or set(row) != {'kind', 'register', 'width'}):
            raise ValueError('A join witness uses an unsupported input constructor')
        if inputs and (type(row['width']) is not int or row['width'] <= 0 or not isinstance(row['register'], str)):
            raise ValueError('A join register input has an invalid width or name')
        rows.append(row)
        tree = tree['right']
        if not isinstance(tree, dict):
            raise ValueError('A join witness spine must end in a source unit')
    if tree != {'kind': 'unit'}:
        raise ValueError('A join witness needs a right-nested register-pair spine')
    return rows


def planned_witnesses(row, layout, roles):
    """Return pending source values; never inspect a target pure equality."""
    from witness_data import closed_bitvector_width as _width
    plan = row.get('join_witness_plan')
    if plan is None:
        return {}, [], None
    if plan.get('schema') != 'source.join-witness-plan.v1':
        raise ValueError('The source join witness schema is unsupported')
    declared = [slot['name'] for slot in layout['declared']]
    remaining = [slot['name'] for slot in layout['remaining']]
    order = plan['ordered_binders']
    if order not in [declared, remaining]:
        raise ValueError('The source join witness order differs from its telescope')
    rows = plan['ordered_witnesses']
    if [item['binder'] for item in rows] != order or _spine(plan['data'], inputs=False) != rows:
        raise ValueError('The source join witness data changes declaration order')
    registers, observed = [], dict(roles)
    for slot in layout['remaining']:
        register = layout['register_slots'].get(slot['name'])
        if register is not None:
            observed[slot['name']] = (register, _width(slot['type']))
        if slot['name'] in observed:
            key = observed[slot['name']]
            if key not in registers:
                registers.append(key)
    expected = [{'kind': 'register', 'register': register, 'width': width}
                for register, width in registers]
    if _spine(plan['input'], inputs=True) != expected:
        raise ValueError('The join input differs from the source-owned register captures')
    projections = {}
    for name, key in observed.items():
        if key in registers:
            term = 'source_words'
            for _ in range(registers.index(key)):
                term = '(snd ' + term + ')'
            projections[name] = '(fst ' + term + ')'
    by_name = {item['binder']: item for item in rows}
    pending = {}
    for slot in layout['remaining']:
        item = by_name[slot['name']]
        value = item['expression']
        if value.get('op') != 'input' or set(value) - {'op', 'width', 'value'}:
            raise ValueError('The source join witness expression needs an explicit input view')
        if slot['name'] in observed:
            if value.get('value') != slot['name'] or value.get('width') != observed[slot['name']][1]:
                raise ValueError('A direct register witness changed its observed value')
            continue
        if 'list' in {token for token, _ in rocq_tokens(slot['type'])}:
            raise ValueError('A join memory witness needs explicit array packaging')
        term = expression(value['value'], 'source join witness expression')
        tokens = rocq_tokens(term)
        used = {token for token, _ in tokens if token in projections}
        if not used:
            raise ValueError('A derived join witness must use an observed source register')
        sources = {observed[name][0] for name in used}
        if set(item.get('derived_from', [])) != sources:
            raise ValueError('The derived witness register provenance differs from its source expression')
        for token, position in reversed(tokens):
            if token in used:
                term = term[:position] + projections[token] + term[position + len(token):]
        pending[slot['name']] = term
    return pending, registers, deepcopy(plan)
