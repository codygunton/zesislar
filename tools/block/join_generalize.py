"""Generalize source traversal values without importing proof-state evidence.

Every result remains an untrusted declaration proposal. Edge certificates check
source arithmetic only. They never certify an Iris entailment or a native proof.
"""
from copy import deepcopy
from dataclasses import dataclass, replace
import hashlib
import json
from pathlib import Path
import re

try:
    from .guard_normal_form import GuardNormalForm
    from .symbolic_state import Expr, bits, input_expr, operation
except ImportError:
    from guard_normal_form import GuardNormalForm
    from symbolic_state import Expr, bits, input_expr, operation


REGISTER = re.compile(r'x(?:[0-9]|[12][0-9]|3[01])\Z')


def continuation_observables(expression, source_bindings):
    """Read value observables from bound exit-resource declarations.

    An independent existential register value is ownership, not an observable
    result value. A fixed value or a value mentioned by another clause remains
    observable. Unknown resource heads refuse rather than hide a dependency.
    """
    try:
        from .entry_seed import definition_body
        from .forward_resources import parse_source_ownership, _strip_enclosure
        from .check_data_only_lemmas import atom, rocq_tokens
    except ImportError:
        from entry_seed import definition_body
        from forward_resources import parse_source_ownership, _strip_enclosure
        from check_data_only_lemmas import atom, rocq_tokens
    declarations, used, registers = {}, set(), set()
    for binding in source_bindings:
        data = Path(binding['path']).read_bytes()
        if hashlib.sha256(data).hexdigest() != binding['sha256']:
            raise ValueError('A continuation source changed')
        name = binding['declaration']
        if name in declarations:
            raise ValueError('A continuation resource head is ambiguous')
        declarations[name] = definition_body(data.decode(), name)

    def inspect(body, active=()):
        body = _strip_enclosure(body)
        if body.startswith('instr_pre '):
            tokens = list(rocq_tokens(body))
            _, end = atom([token for token, _ in tokens], 1)
            if end >= len(tokens):
                raise ValueError('A continuation has no exit resources')
            return inspect(body[tokens[end][1]:], active)
        ownership = parse_source_ownership(body, provenance={})
        locals_ = set()
        for prefix in ownership['existential_prefixes']:
            text = prefix[1:-1].strip()
            groups = re.findall(r"\(([^():]+):[^()]+\)", text)
            if groups and ''.join(re.findall(r"\([^()]+\)", text)).replace(' ', '') == text.replace(' ', ''):
                locals_.update(name for group in groups for name in group.split())
            elif '(' not in text and ':' in text:
                locals_.update(text.split(':', 1)[0].split())
            # Unsupported binder shapes conservatively keep every value live.
        for component in ownership['components']:
            source = _strip_enclosure(component['source'])
            if component['kind'] == 'register':
                value = component['value']
                word = _strip_enclosure(value[len('RVal_Bits '):]) if value.startswith('RVal_Bits ') else ''
                variable = word.split(':', 1)[0].strip()
                elsewhere = ' '.join(other['source'] for other in ownership['components'] if other is not component)
                mentioned = bool(re.search(r"(?<![\w'])" + re.escape(variable) + r"(?![\w'])", elsewhere)) if variable else True
                if variable not in locals_ or mentioned:
                    registers.add(component['name'])
            elif (component['kind'] in {'byte_array', 'unknown_byte_array'} or source == 'True'
                  or source.startswith('⌜') or source.startswith('reg_col ')):
                continue
            else:
                head = source.split(None, 1)[0]
                if head not in declarations or head in active:
                    raise ValueError('A continuation resource needs an acyclic source binding: ' + head)
                used.add(head)
                inspect(declarations[head], (*active, head))
    inspect(expression)
    if used != set(declarations):
        raise ValueError('The continuation includes unused declaration bindings')
    return {'root_expression': expression, 'registers': sorted(registers),
            'source_bindings': deepcopy(source_bindings), 'proof_established': False}


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


def anti_unify(paths, *, names, reserved_names=(), force_keys=()):
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
    if set(force_keys) - set(names):
        raise ValueError('A forced join binder has no owned value')
    result, binders, substitutions = {}, [], [{} for _ in paths]
    for key, name in names.items():
        if not re.fullmatch(r"[A-Za-z][A-Za-z0-9_']*", name):
            raise ValueError('A join binder name is invalid')
        values = [normalize(path[key]) for path in paths]
        widths = {value.width for value in values}
        if len(widths) != 1 or type(values[0].width) is not int or values[0].width <= 0:
            raise ValueError('A join value needs one closed positive width')
        if key not in force_keys and all(value == values[0] for value in values[1:]):
            result[key] = values[0]
            continue
        def contains_name(value):
            return ((value.op == 'input' and re.search(r"(?<![\w'])" + re.escape(name) + r"(?![\w'])",
                                                       str(value.value)))
                    or any(contains_name(arg) for arg in value.args))
        if name in reserved_names or any(contains_name(value) for path in paths for value in path.values()):
            raise ValueError('A join binder captures a source input: ' + name)
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


def witness_plan(binders, *, register_bindings, source_bindings=None, source_context=None,
                 array_bindings=None):
    """Use only the selector's existing register/pair input constructors.

    array_bindings maps a binder to the owned byte array whose value it is.
    """
    inputs, witnesses = [], []
    array_bindings = array_bindings or {}
    sources = {}
    if source_bindings is not None:
        from source_witness_bindings import authenticate_sources
        sources = authenticate_sources(binders, source_bindings, source_context)
        if set(register_bindings) & set(source_bindings):
            raise ValueError('A witness has two competing source readers.')
        if set(register_bindings) | set(source_bindings) != {b['name'] for b in binders}:
            raise ValueError('The typed source mapping has missing or extra witness slots.')
    for binder in binders:
        name = binder['name']
        if name in sources:
            inputs.append(sources[name])
            witnesses.append({'binder': name, 'source_key': sources[name]['source_key'],
                              'type': binder['type']})
            continue
        if name in array_bindings and name not in register_bindings:
            inputs.append({'kind': 'owned_array', 'resource_id': array_bindings[name]})
            witnesses.append({'binder': name, 'resource_id': array_bindings[name], 'type': binder['type']})
            continue
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
    result = {'schema': 'source.join-witness-plan.v1', 'ordered_binders': [b['name'] for b in binders],
              'input': nested(inputs, {'kind': 'unit'}), 'ordered_witnesses': witnesses,
              'data': nested(witnesses, {'kind': 'unit'})}
    if source_bindings is not None:
        result.update(schema='source.join-witness-plan.v2', input_family='authenticated_source',
                      source_context=deepcopy(source_context), source_bindings=deepcopy(source_bindings))
    return result


def validate_edges(plan, *, refutations=()):
    """Reject missing or invalid source certificates without executing Rocq."""
    if refutations:
        from join_refutations import validate_refutations
        validate_refutations(plan, refutations)
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
            if relation['kind'] == 'source_equality':
                expression = normalize(Expr.from_dict(relation['expression']))
                value = normalize(bindings[input_expr(relation['binder'], relation['width'])])
                if value != expression or expression.op == 'bits':
                    raise ValueError('A source equality changes an owned edge value')
                if relation['coq'] != '(' + relation['binder'] + ' = ' + expression.coq() + ')':
                    raise ValueError('A source equality has a different rendered relation')
                continue
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


def binder_names(paths, register_order, reserved_names=()):
    """Name each register binder machine_<register>, or a fresh suffix of it.

    A join downstream of another join seed sees that seed's binders as source
    inputs. A suffix keeps the new binder distinct; without a collision the
    name is unchanged.
    """
    taken = set(reserved_names)

    def inputs(value):
        found = {str(value.value)} if value.op == 'input' else set()
        for arg in value.args:
            found |= inputs(arg)
        return found

    for path in paths:
        for value in path.values():
            for text in inputs(value):
                taken.update(re.findall(r"[A-Za-z][A-Za-z0-9_']*", text))
    names = {}
    for register in register_order:
        name, index = 'machine_' + register, 0
        while name in taken:
            index += 1
            name = 'machine_' + register + '_' + str(index)
        names[register] = name
        taken.add(name)
    return names


def generalize_registers(alternatives, *, register_order, reserved_names=(), dead_registers=(),
                         relational_registers=()):
    """Prepare a register-only join core from complete source alternatives."""
    if len(set(register_order)) != len(register_order) or not register_order:
        raise ValueError('A join needs a unique owned register order')
    if any(not REGISTER.fullmatch(register) for register in register_order):
        raise ValueError('A join cannot generalize a system register')
    if set(relational_registers) - set(register_order) or set(relational_registers) & set(dead_registers):
        raise ValueError('A relational register must have a live owned value')
    paths, conditions = [], []
    for alternative in alternatives:
        state = alternative['state']
        registers = {**state.get('retained_registers', {}), **state['registers']}
        if any(register not in registers for register in register_order):
            raise ValueError('A join edge lost an owned register value')
        paths.append({register: Expr.from_dict(registers[register]) for register in register_order})
        conditions.append([Expr.from_dict(value) for value in state['conditions']])
    unified = anti_unify(paths, names=binder_names(paths, register_order, reserved_names),
                        reserved_names=reserved_names, force_keys=set(dead_registers) | set(relational_registers))
    relations, refusals = [], []
    for binder in unified.binders:
        if binder['value_key'] in dead_registers:
            continue
        if binder['value_key'] in relational_registers:
            values = [normalize(path[binder['value_key']]) for path in paths]
            if not all(value == values[0] for value in values[1:]):
                raise ValueError('A requested source equality differs across incoming edges')
            if values[0].op == 'bits':
                raise ValueError('A source equality cannot fix a successor to a branch literal')
            relations.append({'kind': 'source_equality', 'binder': binder['name'],
                              'width': values[0].width, 'expression': values[0].to_dict(),
                              'coq': '(' + binder['name'] + ' = ' + values[0].coq() + ')'})
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
    plan['generalized_values'] = [{'register': register, 'reason': 'dead_before_cut_or_return',
        'edge_values': [path[register].to_dict() for path in paths]} for register in register_order
        if register in dead_registers]
    validate_edges(plan)
    return plan


def common_conditions(alternatives, plan):
    """Preserve exact common guards before deriving binder-correlated guards."""
    paths = [[normalize(Expr.from_dict(value)) for value in alternative['state']['conditions']]
             for alternative in alternatives]
    exact = [value for index, value in enumerate(paths[0])
             if value not in paths[0][:index] and all(value in path for path in paths[1:])]
    renamed = []
    def symbolic(value):
        return (value.op not in {'bits', 'enum'} and
                (not value.args or any(symbolic(child) for child in value.args)))
    for path, edge in zip(paths, plan['edges']):
        mapping = {}
        for binder in plan['binders']:
            value = normalize(Expr.from_dict(edge['widened_substitution'][binder['name']]))
            # Replacing a constant would also replace unrelated guard literals.
            if symbolic(value):
                mapping.setdefault(value, input_expr(binder['name'], value.width))
        renamed.append([substitute(value, mapping) for value in path])
    correlated = [value for index, value in enumerate(renamed[0])
                  if value not in renamed[0][:index] and all(value in path for path in renamed[1:])]
    return exact + [value for value in correlated if value not in exact]


def _remove_terminal(tree, terminal_id):
    kind = tree['kind']
    if kind == 'component':
        return None if tree['id'] == terminal_id else deepcopy(tree)
    if kind == 'exists':
        result = deepcopy(tree)
        result['body'] = _remove_terminal(tree['body'], terminal_id)
        if result['body'] is None:
            raise ValueError('A continuation cannot erase an existential scope')
        return result
    if kind == 'sep_list':
        children = [_remove_terminal(child, terminal_id) for child in tree['children']]
        return {**deepcopy(tree), 'children': [child for child in children if child is not None]}
    if kind == 'sep':
        left, right = (_remove_terminal(tree[key], terminal_id) for key in ('left', 'right'))
        if left is None or right is None:
            raise ValueError('The terminal has an unsupported separation scope')
        return {**deepcopy(tree), 'left': left, 'right': right}
    raise ValueError('The join ownership tree has an unsupported node')


def _memory_basis(states, plan, original_seed):
    expressions = {name: Expr.from_dict(value) for name, value in plan['values'].items()}
    registers = [{**state.retained_registers, **state.registers} for state in states]
    basis = {name: [state[name] for state in registers] for name in expressions}
    old_binders = [binder['name'] for binder in original_seed.ownership.get('binders', [])]
    for register, value in original_seed.state.registers.items():
        if not REGISTER.fullmatch(register) or value.op in {'bits', 'bool', 'enum'} or value in expressions.values():
            continue
        text = value.coq()
        if any(re.search(r"(?<![\w'])" + re.escape(name) + r"(?![\w'])", text) for name in old_binders):
            continue
        name = 'source_parameter_' + str(len(expressions))
        expressions[name] = value
        basis[name] = [value] * len(states)
    return basis, expressions


def align_join_edges(alternatives, ownership, terminal_id, continuation_name, keep_binders=False):
    """Express edges that come through an earlier join seed on the original tree.

    A join seed keeps the original components, adds its relation facts as
    `join_relation_*` components (its state keeps them as conditions), moves
    the terminal outside its witness scope as the continuation, and has its
    own binders. Such an edge is rewritten onto the original tree with the
    original terminal. Its binders are returned so the new join keeps them as
    existential binders; with keep_binders the rewritten tree binds them too.
    Any other difference is left for the caller to refuse.
    """
    original = ownership['tree']
    terminal_source = next(component['source'] for component in ownership['components']
                           if component['id'] == terminal_id)
    expected = _remove_terminal(original, terminal_id)
    aligned, extra = [], []
    for alternative in alternatives:
        boundary = alternative.get('resource_boundary', {})
        tree = boundary.get('tree')
        if tree == original or not isinstance(tree, dict) or tree.get('kind') != 'sep':
            aligned.append(alternative)
            continue
        left, right = tree.get('left', {}), tree.get('right')
        terminal = [component for component in boundary.get('components', [])
                    if component['id'] == terminal_id]
        relations = set()
        body = left.get('body') or {}
        if body.get('kind') == 'sep_list':
            relations = {child.get('id') for child in body['children']
                         if str(child.get('id', '')).startswith(('join_relation_', 'join_design_'))}
            body = {**body, 'children': [child for child in body['children']
                                         if child.get('id') not in relations]}
        shape = {key: value for key, value in left.items() if key not in ('binders', 'scope', 'body')}
        expected_shape = {key: value for key, value in expected.items() if key not in ('binders', 'scope', 'body')}
        if (right != {'kind': 'component', 'id': terminal_id} or left.get('kind') != 'exists'
                or shape != expected_shape or body != expected.get('body') or len(terminal) != 1
                or terminal[0]['source'] != continuation_name):
            aligned.append(alternative)
            continue
        names = {binder['name'] for binder in original.get('binders', [])}
        own = [{key: value for key, value in binder.items() if key != 'value_key'}
               for binder in left['binders'] if binder['name'] not in names]
        for binder in own:
            if binder['name'] not in [row['name'] for row in extra]:
                extra.append(binder)
        edge = deepcopy(alternative)
        rewritten = deepcopy(original)
        if keep_binders:
            rewritten['binders'] = [*rewritten.get('binders', []), *deepcopy(own)]
        edge['resource_boundary']['tree'] = rewritten
        edge['resource_boundary']['components'] = [
            {**component, 'source': terminal_source} if component['id'] == terminal_id else component
            for component in edge['resource_boundary']['components'] if component['id'] not in relations]
        aligned.append(edge)
    return aligned, extra


def _write_steps(image, resource_id):
    """The writes of an edge's image into one resource: address, size, value, offset."""
    return tuple((json.dumps(image.writes[step['write_index']].address.to_dict(), sort_keys=True),
                  image.writes[step['write_index']].size,
                  json.dumps(image.writes[step['write_index']].value.to_dict(), sort_keys=True), step['offset'])
                 for step in image.transitions if step['resource_id'] == resource_id)


def generalize_owned_join(alternatives, *, original_seed, entry_pc, vocabulary,
                          continuation, outer_names=(), liveness=None, observables=None,
                          relational_registers=(), design_facts=()):
    """Build a seed when every incoming non-register resource is identical.

    design_facts are join-design conjuncts (Coq text). `{bytes@ADDR}` names the
    current value of the owned array at ADDR; each fact is a pure component of
    the join scope, which the edges into the join must establish.

    This first case needs no memory witness. A differing memory image refuses
    here until affine elimination or whole-array packaging supplies its binder.
    continuation binds the Level1 exit expression as a local K, not a premise.
    """
    try:
        from .forward_resource_design import _state_from_result
        from .forward_resources import parse_source_ownership, render_resource_boundary, apply_owned_writes
        from .resource_seed import OwnedSeed
        from .symbolic_state import MemoryRegion
    except ImportError:
        from forward_resource_design import _state_from_result
        from forward_resources import parse_source_ownership, render_resource_boundary, apply_owned_writes
        from resource_seed import OwnedSeed
        from symbolic_state import MemoryRegion
    if not alternatives:
        raise ValueError('An owned join has no incoming paths')
    if (not isinstance(continuation, dict) or set(continuation) != {'name', 'coq', 'source_binding', 'terminal_id'}
            or not continuation['source_binding'] or not continuation['coq']):
        raise ValueError('An owned join needs a source-bound outer continuation')
    name, terminal_id = continuation['name'], continuation['terminal_id']
    if not re.fullmatch(r'[A-Za-z][A-Za-z0-9_]*', name) or name in outer_names:
        raise ValueError('The continuation captures an outer input')
    ownership = deepcopy(original_seed.ownership)
    original_binders = ownership.get('binders', [])
    if any(binder['name'] == name for binder in original_binders):
        raise ValueError('The continuation captures a source binder')
    register_order = [component['name'] for component in ownership['components'] if component['kind'] == 'register']
    alternatives, inherited_binders = align_join_edges(alternatives, ownership, terminal_id, name)
    dead = set()
    if liveness is not None or observables is not None:
        if (not isinstance(liveness, dict) or liveness.get('pc') != hex(entry_pc)
                or not liveness.get('source_bindings') or not isinstance(observables, dict)
                or not observables.get('source_bindings') or not observables.get('root_expression')):
            raise ValueError('Dead register generalization needs bound liveness and continuation observables')
        if observables['root_expression'] != continuation['coq']:
            raise ValueError('The value observables belong to another continuation')
        live = set(liveness['registers']) | set(observables['registers'])
        dead = set(register_order) - live
    plan = generalize_registers(alternatives, register_order=register_order,
                               reserved_names=[*outer_names, name, *(b['name'] for b in original_binders)],
                               dead_registers=dead, relational_registers=relational_registers)
    if liveness is not None:
        plan['deadness_basis'] = {'liveness': deepcopy(liveness), 'observables': deepcopy(observables)}
    records = []
    for alternative in alternatives:
        boundary = alternative['resource_boundary']
        if boundary.get('block_status') != 'completed' or boundary.get('tree') != ownership['tree']:
            raise ValueError('A join edge has incomplete or different ownership')
        components = {component['id']: component for component in boundary['components']}
        if len(components) != len(boundary['components']) or set(components) != {c['id'] for c in ownership['components']}:
            raise ValueError('A join edge changes the owned resource set')
        records.append(components)
    states = [_state_from_result(alternative['state']) for alternative in alternatives]
    first = states[0]
    if any(state.registers.get('PC') != bits(entry_pc, 64) for state in states):
        raise ValueError('A join edge reaches another program counter')
    images = [apply_owned_writes(original_seed.resources, state.writes, conditions=state.conditions,
                                facts=original_seed.facts, endianness=state.endianness) for state in states]
    if any(image.status != 'complete' for image in images):
        raise ValueError('A join edge cannot authenticate its complete write image')
    # System state is never generalized. Every path must retain the same value.
    for state in states[1:]:
        left = {key: value for key, value in first.registers.items() if not REGISTER.fullmatch(key)}
        right = {key: value for key, value in state.registers.items() if not REGISTER.fullmatch(key)}
        if left != right:
            raise ValueError('A join changes system state')
    resources, components, carried_writes = [], [], []
    memory_by_id = {resource.id: resource for resource in original_seed.resources}
    memory_basis, memory_expressions = _memory_basis(states, plan, original_seed)
    plan['memory_relations'] = []
    for component in ownership['components']:
        key = component['id']
        current = deepcopy(component)
        if component['kind'] != 'register':
            source = records[0][key]['source']
            if any(record[key]['source'] != source for record in records[1:]):
                if key not in memory_by_id:
                    raise ValueError('A non-memory join resource differs: ' + key)
                try:
                    from .join_memory import affine_memory_image
                except ImportError:
                    from join_memory import affine_memory_image
                paths = [[(image.writes[step['write_index']], step['offset']) for step in image.transitions
                          if step['resource_id'] == key] for image in images]
                reconstruction = affine_memory_image(memory_by_id[key], paths, basis=memory_basis,
                    expressions=memory_expressions, register_names=register_order, vocabulary=vocabulary)
                old = memory_by_id[key]
                length = (str(old.length) if isinstance(old.length, int) else
                          'List.length (' + component['value'] + ')' if component.get('value') else None)
                if reconstruction['status'] != 'generated' and length is not None:
                    # Whole-array packaging: the edges disagree on the bytes, so the
                    # join owns an existential array of the same length. An
                    # uninitialized byte on an edge is any byte, so this weakens soundly.
                    binder = 'join_' + key + '_bytes'
                    fraction = component.get('fraction') or ''
                    reconstruction = {'status': 'generated', 'kind': 'array_packaging', 'resource_id': key,
                                      'binder': binder, 'length': length,
                                      'source': '%s ↦ₘ%s∗ %s' % (old.address_z, fraction, binder),
                                      'coq': '(List.length %s = %s)%%nat' % (binder, length),
                                      'detail': reconstruction['detail']}
                if reconstruction['status'] != 'generated':
                    raise ValueError('A join memory value needs explicit array packaging: ' + key + ': ' + reconstruction['detail'])
                source = reconstruction['source']
                plan['memory_relations'].append(reconstruction)
            current['source'] = source
        if key == terminal_id:
            if component['kind'] != 'opaque' or current['source'] != 'True':
                raise ValueError('The selected inventory terminal is not True')
            continue
        if key in memory_by_id:
            old = memory_by_id[key]
            if (old.byte_array is None and current['source'] == component['source']
                    and not any(image.updates[key] for image in images)):
                # No edge wrote this uninitialized span; it joins unchanged.
                resources.append(old)
                components.append(current)
                continue
            pieces = parse_source_ownership(current['source'], provenance=current['provenance'])['components']
            if (old.byte_array is None and len(pieces) > 1
                    and len({_write_steps(image, key) for image in images}) == 1):
                # Every edge wrote the same bytes into this uninitialized span, so every edge
                # states the same pieces: the written runs and the unwritten gaps. The join
                # keeps them exactly; its seed carries those writes for the successors.
                resources.append(old)
                components.append(current)
                carried_writes += [images[0].writes[step['write_index']] for step in images[0].transitions
                                   if step['resource_id'] == key]
                continue
            if len(pieces) != 1:
                raise ValueError('A join edge writes only part of an owned span differently: ' + key)
            parsed, = pieces
            if parsed['kind'] != 'byte_array':
                raise ValueError('An owned join array has no complete incoming image')
            current.update(kind='byte_array', value=parsed['value'], address_z=parsed['address_z'],
                           fraction=parsed.get('fraction'))
            resources.append(replace(old, byte_array=input_expr(parsed['value'], None), component=current))
        components.append(current)
    if terminal_id not in records[0]:
        raise ValueError('The continuation replaces no inventory terminal')
    state = first.copy()
    for interval in original_seed.state.source_intervals:
        if interval not in state.source_intervals:
            state.source_intervals.append(deepcopy(interval))
    for alignment in original_seed.state.source_alignments:
        if alignment not in state.source_alignments:
            state.source_alignments.append(deepcopy(alignment))
    state.registers = {key: value for key, value in state.registers.items() if not REGISTER.fullmatch(key)}
    state.registers.update({key: Expr.from_dict(value) for key, value in plan['values'].items()})
    state.retained_registers = dict(state.registers)
    # Exact intersection preserves source facts without choosing a path.
    state.conditions = common_conditions(alternatives, plan)
    plan['common_guards'] = [value.to_dict() for value in state.conditions]
    plan['common_guard_certificates'] = []
    for guard in state.conditions:
        matches = []
        for edge in plan['edges']:
            originals = [normalize(Expr.from_dict(value)) for value in edge['original_conditions']]
            bindings = {input_expr(binder['name'], int(binder['type'].split()[1])):
                        normalize(Expr.from_dict(edge['widened_substitution'][binder['name']]))
                        for binder in plan['binders']}
            restored = substitute(guard, bindings)
            if guard in originals:
                matches.append({'edge': edge['index'], 'condition': originals.index(guard),
                                'kind': 'exact_source_guard'})
            elif restored in originals:
                matches.append({'edge': edge['index'], 'condition': originals.index(restored),
                                'kind': 'source_substitution'})
            else:
                raise ValueError('A common guard has no source condition on every edge')
        plan['common_guard_certificates'].append({'guard': guard.to_dict(), 'edges': matches})
    for relation in plan['relations']:
        word = input_expr(relation['binder'], relation['width'])
        if relation['kind'] == 'source_equality':
            state.conditions.append(operation('=', word, Expr.from_dict(relation['expression'])))
        else:
            state.conditions.extend([operation('bvuge', word, bits(relation['lower'], word.width)),
                                     operation('bvule', word, bits(relation['upper'], word.width))])
    state.writes, state.reports, state.register_writes = list(carried_writes), [], []
    state.memory = []

    def stored_byte(index, resource_id, offset):
        """Return the byte an edge holds at offset: its own write, else its seed's known byte."""
        update = images[index].updates[resource_id].get(offset)
        if update is not None:
            return normalize(Expr.from_dict(update['value']))
        # An edge through an earlier join seed keeps the seed's stored bytes in its memory.
        for region in states[index].memory:
            if region.ownership_id == resource_id and offset < len(region.bytes):
                return normalize(region.bytes[offset])
        return None

    for resource in resources:
        prefix = []
        offset = 0
        while True:
            value = stored_byte(0, resource.id, offset)
            if value is None or any(stored_byte(index, resource.id, offset) != value
                                    for index in range(1, len(images))):
                break
            prefix.append(value)
            offset += 1
        state.memory.append(MemoryRegion(resource.base, tuple(prefix), resource.byte_array, resource.length,
                                         uninitialized=resource.byte_array is None, ownership_id=resource.id))
    state.trace_count = 0
    def source_inputs(value):
        return ([str(value.value)] if value.op == 'input' else []) + [
            text for child in value.args for text in source_inputs(child)]
    source_text = ' '.join([*(component['source'] for component in components if component['kind'] != 'register'),
                            *(text for value in state.registers.values() for text in source_inputs(value)),
                            *(text for value in state.conditions for text in source_inputs(value))])
    used_binders = [binder for binder in [*original_binders, *({**row, 'scope': []} for row in inherited_binders)]
                    if re.search(r"(?<![\w'])" + re.escape(binder['name']) + r"(?![\w'])", source_text)]
    # The inherited source has one explicit witness scope. Nested scopes need
    # their own packaging design rather than moving a binder across a wand.
    tree = _remove_terminal(ownership['tree'], terminal_id)
    if tree['kind'] != 'exists' or any(binder['scope'] != [] for binder in original_binders):
        raise ValueError('The join needs one explicit source witness scope')
    additions = [{**binder, 'expression': input_expr(binder['name'], int(binder['type'].split()[1])).to_dict()}
                 for binder in plan['binders']]
    additions += [{'name': row['binder'], 'type': 'list byte', 'expression': input_expr(row['binder'], None).to_dict()}
                  for row in plan['memory_relations'] if row.get('kind') == 'array_packaging']
    available = {binder['name']: binder for binder in [*used_binders, *additions]}
    ordered = []
    for register in register_order:
        value = state.registers[register]
        for binder in available.values():
            if binder not in ordered and str(binder['name']) in source_inputs(value):
                ordered.append(binder)
    ordered.extend(binder for binder in available.values() if binder not in ordered)
    tree['binders'] = [{key: value for key, value in binder.items() if key != 'scope'} for binder in ordered]
    ownership['binders'] = [{**binder, 'scope': [0]} for binder in ordered]
    tree['scope'] = [0]
    for component in components:
        component['scope'] = [[0] if scope == [] else scope for scope in component.get('scope', [])]
    if tree['body']['kind'] != 'sep_list':
        raise ValueError('The join relation scope is not an owned resource list')
    for index, relation in enumerate(plan['relations']):
        key = f'join_relation_{index}'
        if key in records[0]:
            raise ValueError('A join relation captures an owned resource identifier')
        components.append({'id': key, 'kind': 'opaque', 'source': '⌜' + relation['coq'] + '⌝', 'scope': [[0]],
                           'provenance': {'join_edge_count': len(alternatives), 'relation': deepcopy(relation)}})
        tree['body']['children'].append({'kind': 'component', 'id': key})
    values = {component.get('address_z'): component.get('value') for component in components
              if component['kind'] == 'byte_array'}
    for index, fact in enumerate(design_facts):
        def array_value(match):
            if match[1] not in values:
                raise ValueError('A join design names no owned array at ' + match[1])
            return values[match[1]]
        text = re.sub(r'\{bytes@([^}]*)\}', array_value, fact)
        key = f'join_design_{index}'
        components.append({'id': key, 'kind': 'opaque', 'source': '⌜' + text + '⌝', 'scope': [[0]],
                           'provenance': {'join_design': fact}})
        tree['body']['children'].append({'kind': 'component', 'id': key})
    packaged = [row for row in plan['memory_relations'] if row.get('kind') == 'array_packaging']
    for index, row in enumerate(packaged, start=len(plan['relations'])):
        key = f'join_relation_{index}'
        components.append({'id': key, 'kind': 'opaque', 'source': '⌜' + row['coq'] + '⌝', 'scope': [[0]],
                           'provenance': {'join_edge_count': len(alternatives), 'relation': deepcopy(row)}})
        tree['body']['children'].append({'kind': 'component', 'id': key})
    provenance = {'contract_exit': deepcopy(continuation['source_binding'])}
    components.append({'id': terminal_id, 'kind': 'opaque', 'source': name, 'scope': [],
                       'provenance': provenance, 'seed_component': {'kind': 'opaque', 'coq': name}})
    ownership.update(tree={'kind': 'sep', 'left': tree, 'right': {'kind': 'component', 'id': terminal_id}},
                     components=components, existential_prefixes=[])
    register_bindings = {}
    for binder in ordered:
        for register in register_order:
            value = state.registers[register]
            if value == input_expr(binder['name'], value.width):
                register_bindings.setdefault(binder['name'], (register, value.width))
    array_bindings = {component['value']: component['id'] for component in components
                      if component['kind'] == 'byte_array' and component.get('value') in
                      {binder['name'] for binder in ordered}}
    full_witness_plan = witness_plan(ordered, register_bindings=register_bindings,
                                     array_bindings=array_bindings)
    owned_edges = []
    for edge in plan['edges']:
        record = deepcopy(edge)
        # An array witness is the inherited array value, the same on every edge.
        record['ordered_witnesses'] = [{'binder': binder['name'],
            'expression': deepcopy(edge['original_values'][register_bindings[binder['name']][0]])
            if binder['name'] in register_bindings else input_expr(binder['name'], None).to_dict()}
            for binder in ordered]
        record['widened_substitution'] = {row['binder']: row['expression'] for row in record['ordered_witnesses']}
        owned_edges.append(record)
    plan.update(owned_binders=deepcopy(ordered), owned_edges=owned_edges, join_witness_plan=full_witness_plan)
    seed = OwnedSeed(state, ownership, resources, deepcopy(original_seed.facts), [],
                     deepcopy(plan['join_refusals']), owned_edges, full_witness_plan, 'join')
    rendered = render_resource_boundary(ownership, apply_owned_writes(resources, [], facts=seed.facts),
                                        state, vocabulary=vocabulary)
    if rendered['block_status'] != 'completed':
        raise ValueError('The generalized join ownership cannot render')
    boundary = {'pc': hex(entry_pc), 'status': 'generated_join', 'alternatives': [
        {'predecessor_pc': None, 'seed_pc': hex(entry_pc), 'path': [], 'state': state.to_dict(),
         'resource_boundary': rendered}]}
    return {'seed': seed, 'plan': plan, 'boundary': boundary, 'continuation': deepcopy(continuation)}


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


def attach_exit_pullback(join, traversal, *, output_resource_id, return_expression, allows, vocabulary):
    """Attach the contract relation only after checking every traversal stop."""
    try:
        from .forward_resource_design import _state_from_result
        from .forward_resources import apply_owned_writes, parse_source_ownership, render_resource_boundary
    except ImportError:
        from forward_resource_design import _state_from_result
        from forward_resources import apply_owned_writes, parse_source_ownership, render_resource_boundary
    seed, exits, obligations = join['seed'], [], []
    for stop in traversal['stops']:
        if stop['reason'] == 'infeasible':
            obligations.append({'path': deepcopy(stop['path']), 'state': deepcopy(stop.get('state')),
                                'proof_status': 'open', 'required_rocq_guard_projection': True})
            continue
        if (stop['reason'] != 'unknown_pc' or stop.get('stage') != 'block_exit'
                or normalize(Expr.from_dict(stop['actual_pc'])) != normalize(return_expression)):
            refusal = {'kind': 'join_exit_pullback_refusal', 'reason': stop['reason'],
                       'path': deepcopy(stop.get('path')), 'actual_pc': deepcopy(stop.get('actual_pc'))}
            return {**join, 'pullback': {'status': 'refused', **refusal}}
        state = _state_from_result(stop['state'])
        image = apply_owned_writes(seed.resources, state.writes, conditions=state.conditions, facts=seed.facts,
                                   endianness=state.endianness)
        boundary = render_resource_boundary(seed.ownership, image, state, vocabulary=vocabulary)
        if boundary['block_status'] != 'completed':
            return {**join, 'pullback': {'status': 'refused', 'kind': 'join_exit_pullback_refusal',
                                       'reason': 'incomplete_final_ownership'}}
        components = [component for component in boundary['components'] if component['id'] == output_resource_id]
        if len(components) != 1:
            raise ValueError('The exit image has no unique owned output resource')
        parsed = parse_source_ownership(components[0]['source'], provenance=components[0]['provenance'])
        if len(parsed['components']) != 1 or parsed['components'][0]['kind'] != 'byte_array':
            return {**join, 'pullback': {'status': 'refused', 'kind': 'join_exit_pullback_refusal',
                                       'reason': 'incomplete_final_output_array'}}
        exits.append({'kind': 'symbolic_return', 'return': return_expression.to_dict(),
                      'image': parsed['components'][0]['value']})
    pullback = exit_pullback(exits, allows=allows)
    pullback['source_refutations'] = obligations
    if pullback['status'] != 'generated':
        return {**join, 'pullback': pullback}
    owned = deepcopy(seed)
    key = 'join_exit_meaning'
    if any(component['id'] == key for component in owned.ownership['components']):
        raise ValueError('The exit meaning captures an owned resource identifier')
    source = '⌜(' + allows['application'] + ') (' + pullback['image'] + ')⌝'
    owned.ownership['components'].insert(-1, {'id': key, 'kind': 'opaque', 'source': source, 'scope': [[0]],
        'provenance': {'contract_allows': deepcopy(allows['source_binding']), 'proof_established': False}})
    owned.ownership['tree']['left']['body']['children'].append({'kind': 'component', 'id': key})
    body = render_resource_boundary(owned.ownership, apply_owned_writes(owned.resources, [], facts=owned.facts),
                                    owned.state, vocabulary=vocabulary)
    boundary = deepcopy(join['boundary'])
    boundary['alternatives'][0]['resource_boundary'] = body
    return {**join, 'seed': owned, 'boundary': boundary, 'pullback': pullback}
