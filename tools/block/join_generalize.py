"""Generalize source traversal values without importing proof-state evidence.

Every result remains an untrusted declaration proposal. Edge certificates check
source arithmetic only. They never certify an Iris entailment or a native proof.
"""
from copy import deepcopy
from dataclasses import dataclass
import re

try:
    from .guard_normal_form import GuardNormalForm
    from .symbolic_state import Expr, bits, input_expr, operation
except ImportError:
    from guard_normal_form import GuardNormalForm
    from symbolic_state import Expr, bits, input_expr, operation


REGISTER = re.compile(r'x(?:[0-9]|[12][0-9]|3[01])\Z')


def normalize(value):
    """Use the traversal's exact, width-checked expression simplifications."""
    if value.op in {'unknown_input', 'unknown_read'}:
        raise ValueError('A join value has no source binding')
    if not value.args:
        return value
    args = tuple(normalize(arg) for arg in value.args)
    return operation(value.op, *args, width=value.width, value=value.value)


def substitute(value, bindings):
    if value in bindings:
        return bindings[value]
    if not value.args:
        return value
    return normalize(Expr(value.op, tuple(substitute(arg, bindings) for arg in value.args),
                          value.width, value.value))


@dataclass
class AntiUnification:
    values: dict
    binders: list
    substitutions: list


def anti_unify(paths, *, names):
    """Keep equal values. Bind every differing value in declaration order.

    names maps each value key to its proposed binder name. The caller supplies
    ordered keys from the owned resource declaration, not sorted register names.
    """
    if not paths or not names:
        raise ValueError('A join needs paths and an explicit declaration order')
    if len(set(names.values())) != len(names):
        raise ValueError('A join repeats a binder name')
    if any(set(path) != set(names) for path in paths):
        raise ValueError('Join paths have different owned value sets')
    result, binders, substitutions = {}, [], [{} for _ in paths]
    for key, name in names.items():
        if not re.fullmatch(r"[A-Za-z][A-Za-z0-9_']*", name):
            raise ValueError('A join binder name is invalid')
        values = [normalize(path[key]) for path in paths]
        widths = {value.width for value in values}
        if len(widths) != 1 or type(values[0].width) is not int or values[0].width <= 0:
            raise ValueError('A join value needs one closed positive width')
        if all(value == values[0] for value in values[1:]):
            result[key] = values[0]
            continue
        width = values[0].width
        result[key] = input_expr(name, width)
        binders.append({'name': name, 'type': f'bv {width}', 'value_key': key})
        for mapping, value in zip(substitutions, values):
            mapping[name] = value
    return AntiUnification(result, binders, substitutions)


def hull(values, conditions, *, name, scalar_ranges=None):
    """Return an F44 bound only when every edge supplies a narrower hull."""
    if len(values) != len(conditions) or not values:
        raise ValueError('A join hull needs conditions for every edge')
    width = values[0].width
    if type(width) is not int or width <= 0 or any(value.width != width for value in values):
        raise ValueError('A join hull needs one closed positive width')
    scalar_ranges = scalar_ranges or [() for _ in values]
    if len(scalar_ranges) != len(values):
        raise ValueError('A join hull needs scalar ranges for every edge')
    intervals = []
    for value, guards, ranges in zip(values, conditions, scalar_ranges):
        normal = GuardNormalForm(guards, scalar_ranges=ranges)
        low, high = normal.interval(normal.unsigned(value))
        if not 0 <= low <= high < 1 << width:
            raise ValueError('A join hull exceeds its bitvector type')
        intervals.append((low, high))
    low, high = min(item[0] for item in intervals), max(item[1] for item in intervals)
    if (low, high) == (0, (1 << width) - 1):
        return None
    return {'kind': 'unsigned_hull', 'binder': name, 'width': width,
            'lower': low, 'upper': high, 'edge_intervals': [list(item) for item in intervals],
            'coq': f'({low}%Z <= bv_unsigned {name} <= {high}%Z)%Z'}


def witness_plan(binders, *, register_bindings):
    """Use only the selector's existing register/pair input constructors."""
    inputs, witnesses = [], []
    for binder in binders:
        name = binder['name']
        if name not in register_bindings:
            raise ValueError('A join witness needs array packaging or an approved input interface: ' + name)
        register, width = register_bindings[name]
        if not REGISTER.fullmatch(register) or type(width) is not int or width <= 0:
            raise ValueError('A join witness has an invalid register input')
        if binder['type'] != f'bv {width}':
            raise ValueError('A join witness width differs from its declaration')
        inputs.append({'kind': 'register', 'register': register, 'width': width})
        witnesses.append({'binder': name, 'expression': input_expr(name, width).to_dict()})

    def nested(items, unit):
        result = unit
        for item in reversed(items):
            result = {'kind': 'pair', 'left': item, 'right': result}
        return result

    # This builds right-nested products in declaration order. It does not
    # reverse the witness sequence supplied to ExplicitWitnessOrder293.
    return {'schema': 'source.join-witness-plan.v1', 'ordered_binders': [b['name'] for b in binders],
            'input': nested(inputs, {'kind': 'unit'}), 'ordered_witnesses': witnesses,
            'data': nested(witnesses, {'kind': 'unit'})}


def validate_edges(plan):
    """Reject missing or invalid source certificates without executing Rocq."""
    binders = plan['binders']
    if len({binder['name'] for binder in binders}) != len(binders):
        raise ValueError('A join repeats a declaration')
    expected = [binder['name'] for binder in binders]
    for edge in plan['edges']:
        if [row['binder'] for row in edge['ordered_witnesses']] != expected:
            raise ValueError('A join edge changes witness declaration order')
        bindings = {input_expr(binder['name'], int(binder['type'].split()[1])):
                    Expr.from_dict(edge['widened_substitution'][binder['name']]) for binder in binders}
        for key, value in plan['values'].items():
            actual = substitute(Expr.from_dict(value), bindings)
            if actual != normalize(Expr.from_dict(edge['original_values'][key])):
                raise ValueError('A join edge changes an owned value')
        for relation in plan['relations']:
            if relation['kind'] != 'unsigned_hull':
                raise ValueError('A join relation has no authorized source validator')
            normal = GuardNormalForm([Expr.from_dict(value) for value in edge['original_conditions']])
            value = bindings[input_expr(relation['binder'], relation['width'])]
            low, high = normal.interval(normal.unsigned(value))
            if list((low, high)) != relation['edge_intervals'][edge['index']]:
                raise ValueError('A join edge changed its interval certificate')
            if not relation['lower'] <= low <= high <= relation['upper']:
                raise ValueError('A join edge does not imply its hull')
    return True


def generalize_registers(alternatives, *, register_order):
    """Prepare a register-only join core from complete source alternatives."""
    if len(set(register_order)) != len(register_order) or not register_order:
        raise ValueError('A join needs a unique owned register order')
    if any(not REGISTER.fullmatch(register) for register in register_order):
        raise ValueError('A join cannot generalize a system register')
    paths, conditions = [], []
    for alternative in alternatives:
        state = alternative['state']
        registers = {**state.get('retained_registers', {}), **state['registers']}
        if any(register not in registers for register in register_order):
            raise ValueError('A join edge lost an owned register value')
        paths.append({register: Expr.from_dict(registers[register]) for register in register_order})
        conditions.append([Expr.from_dict(value) for value in state['conditions']])
    unified = anti_unify(paths, names={register: 'machine_' + register for register in register_order})
    relations, refusals = [], []
    for binder in unified.binders:
        try:
            relation = hull([path[binder['value_key']] for path in paths], conditions, name=binder['name'])
            if relation:
                relations.append(relation)
        except ValueError as error:
            refusals.append({'kind': 'join_hull_refusal', 'binder': binder['name'], 'detail': str(error)})
    edges = []
    for index, (alternative, path, mapping) in enumerate(zip(alternatives, paths, unified.substitutions)):
        edges.append({'index': index, 'predecessor_pc': alternative.get('predecessor_pc'),
            'path': deepcopy(alternative.get('path', [])),
            'ordered_witnesses': [{'binder': binder['name'], 'expression': mapping[binder['name']].to_dict()}
                                  for binder in unified.binders],
            'widened_substitution': {name: value.to_dict() for name, value in mapping.items()},
            'original_values': {name: value.to_dict() for name, value in path.items()},
            'original_conditions': deepcopy(alternative['state']['conditions']),
            'certificate': {'kind': 'source_substitution', 'proof_established': False}})
    plan = {'schema': 'source.join-entry.v1', 'binders': unified.binders,
            'values': {name: value.to_dict() for name, value in unified.values.items()},
            'relations': relations, 'edges': edges, 'join_refusals': refusals,
            'witness_plan': witness_plan(unified.binders, register_bindings={
                binder['name']: (binder['value_key'], unified.values[binder['value_key']].width)
                for binder in unified.binders}), 'proof_established': False}
    validate_edges(plan)
    return plan


def exit_pullback(exits, *, allows):
    """Form one meaning conjunct only for a single symbolic return image.

    The caller runs the block once from the generalized seed. It supplies exact
    feasible exit records and a source-bound contract relation, never a result
    captured from proof search. Memory rendering remains the resource adapter's
    responsibility.
    """
    if not exits:
        return {'status': 'refused', 'kind': 'join_exit_pullback', 'detail': 'No feasible exit exists'}
    if any(exit.get('kind') != 'symbolic_return' for exit in exits):
        return {'status': 'refused', 'kind': 'join_exit_pullback', 'detail': 'The block has another exit'}
    image = exits[0]['image']
    if any(exit['image'] != image or exit.get('return') != exits[0].get('return') for exit in exits[1:]):
        return {'status': 'refused', 'kind': 'join_exit_pullback', 'detail': 'The final images or returns differ'}
    if not isinstance(allows, dict) or not allows.get('source_binding') or not allows.get('application'):
        raise ValueError('An exit pullback needs a source-bound contract relation')
    return {'status': 'generated', 'kind': 'exit_pullback', 'image': deepcopy(image),
            'return': deepcopy(exits[0].get('return')), 'allows': deepcopy(allows),
            'proof_established': False}
