"""Assemble one source loop class without changing its widening algorithm."""
from copy import deepcopy
import re

from forward_resource_design import _state_from_result
from forward_resources import apply_owned_writes, render_resource_boundary
from resource_seed import OwnedSeed
from symbolic_state import Expr, input_expr, operation
from render_support import binders, expression, identifier


def guard_incoming_boundary(boundary, *, source_words, provenance):
    """Bind checked source views before rendering their exact path guards.

    The caller authenticates each view application. This renderer retains that
    application and every original resource; it does not prove an extraction.
    """
    from entry_formatter import SymbolicConditions
    from forward_resources import _render_tree

    if boundary.get('block_status') != 'completed':
        raise ValueError('Incoming guards require a complete resource boundary')
    result = deepcopy(boundary)
    tree = result['tree']
    scope = tree['left'] if tree.get('kind') == 'sep' else tree
    if scope.get('kind') != 'exists' or scope['body'].get('kind') != 'sep_list':
        raise ValueError('Incoming guards need one existing existential scope')
    telescope = scope['binders']
    names = {row['name'] for row in telescope} | {'args', 'returnAddress', 'domain', 'Sigma', 'K'}
    components = {row['id']: row for row in result['components']}
    aliases = {}
    for row in source_words:
        if set(row) != {'name', 'type', 'expression', 'source_view'}:
            raise ValueError('A source word lacks its checked view application')
        name, kind = binders([{'name': row['name'], 'type': row['type']}], names)[0]
        value = Expr.from_dict(row['expression'])
        view = row['source_view']
        owner = components.get(view['owner_id'])
        if (owner is None or owner['source'] != view['owner_source']
                or view['source_expression'] != row['expression']
                or value.op != 'input' or value.value != name
                or value.width is None or kind != 'bv ' + str(value.width)):
            raise ValueError('The source word differs from its owned view')
        if value in aliases:
            raise ValueError('A source word has two view applications')
        aliases[value] = name
        telescope.append({'name': name, 'type': kind})
        names.add(name)
    conditions = SymbolicConditions(lambda context: deepcopy(provenance),
                                    aliases=aliases, normal_form=False)
    guards, refusals = [], []
    for index, raw in enumerate(boundary['path_conditions']):
        try:
            lowered = conditions(raw, {'binders': deepcopy(telescope),
                'condition_index': index, 'path_conditions': boundary['path_conditions']})
            for binder in lowered['existentials']:
                if binder['name'] in names:
                    raise ValueError('A trace witness captures an incoming binder')
                telescope.append(binder)
                names.add(binder['name'])
            terms = [term['term']['value'] for component in lowered['components']
                     for term in component['terms']]
            for offset, term in enumerate(terms):
                key = 'incoming_guard_' + str(index) + '_' + str(offset)
                if key in components:
                    raise ValueError('An incoming guard repeats an ownership identifier')
                component = {'id': key, 'source': '⌜' + term + '⌝',
                             'provenance': {'condition': deepcopy(raw), 'source': deepcopy(provenance)}}
                result['components'].append(component)
                components[key] = component
                scope['body']['children'].append({'kind': 'component', 'id': key})
            guards.append({'condition_index': index, 'expression': deepcopy(raw), 'terms': terms})
        except ValueError as error:
            refusals.append({'condition_index': index, 'expression': deepcopy(raw), 'reason': str(error)})
    result['body'] = _render_tree(tree, {key: row['source'] for key, row in components.items()})
    return {'boundary': result, 'guards': guards, 'refusals': refusals,
            'status': 'rendered' if not refusals else 'refused',
            'source_words': deepcopy(source_words), 'trace_witnesses': deepcopy(conditions.witnesses),
            'proof_established': False}


def _trace_fact_dependencies(value):
    if isinstance(value, dict):
        names = {'condition_dependencies', 'source_conditions', 'trace_conditions',
                 'path_conditions', 'guard', 'guards'}
        return any(key in names or _trace_fact_dependencies(item)
                   for key, item in value.items())
    if isinstance(value, list):
        return any(_trace_fact_dependencies(item) for item in value)
    return False


def assemble_loop_class(source, *, original_seed, vocabulary, continuation, outer_names=(), fold_renderer=None):
    """Keep exact ownership and the accepted minimal condition dependencies."""
    if any(_trace_fact_dependencies(fact) for fact in original_seed.facts):
        raise ValueError('An inherited source fact needs a separate trace-condition justification')
    state = _state_from_result(source['proposed_state'])
    projection = source['relation_condition_projection']
    indices = projection['condition_indices']
    if (any(type(index) is not int or not 0 <= index < len(state.conditions) for index in indices)
            or len(set(indices)) != len(indices)
            or [state.conditions[index].to_dict() for index in indices] != projection['conditions']):
        raise ValueError('The loop condition projection differs from its original state')
    omitted_conditions = [{'kind': 'loop_condition_projection', 'condition_index': index,
        'condition': value.to_dict(), 'source_index': source['source_index'],
        'reason': 'The accepted minimal dependencies do not require this original condition'}
        for index, value in enumerate(state.conditions) if index not in indices]
    state.conditions = [Expr.from_dict(value) for value in projection['conditions']]
    if not source['checked_cursor_relations'] or source['kernel_entailments'] != 'OPEN':
        raise ValueError('The class needs its checked source relations and open kernel obligations')
    required = set()
    for relation in source['checked_cursor_relations'] + source['retained_fold_relations']:
        matches = [row for row in source['minimal_condition_sets'] if row['relation'] == relation]
        if len(matches) != 1:
            raise ValueError('The loop relation lacks one exact minimal dependency set')
        required.update(matches[0]['preheader'])
    if indices != sorted(required):
        raise ValueError('The emitted conditions differ from the checked relation dependencies')
    ownership = deepcopy(original_seed.ownership)
    tree = ownership['tree']
    if tree['kind'] != 'exists' or tree['body']['kind'] != 'sep_list':
        raise ValueError('The loop source needs one explicit owned witness scope')
    terminal = continuation['terminal_id']
    components = ownership['components']
    old_terminal = [item for item in components if item['id'] == terminal]
    if (len(old_terminal) != 1 or old_terminal[0]['source'] != 'True'
            or old_terminal[0]['kind'] != 'opaque'):
        raise ValueError('The loop continuation must replace the exact inventory True leaf')
    rows = source['loop_binders']
    names = [name for name, _ in binders([{'name': row['name'], 'type': row['type']} for row in rows],
                                       set(outer_names) | {'Sigma', continuation['name']})]
    if names != source['loop_witness_plan']['ordered_binders']:
        raise ValueError('The loop binders differ from witness declaration order')
    facts = []
    for row in rows:
        register = row.get('register')
        if register is None:
            if row.get('role') != 'derived':
                raise ValueError('A loop binder has no existing register or derived witness')
            continue
        old = state.registers[register]
        value = input_expr(row['name'], old.width)
        if row['type'] != 'bv ' + str(old.width):
            raise ValueError('The loop register binder changes its bitvector width')
        if row.get('role') == 'observed_alias':
            if old.to_dict() != row['source_expression']:
                raise ValueError('The observed endpoint differs from its bound source expression')
            if row['meaning_link'] != row['name'] + ' = ' + old.coq():
                raise ValueError('The endpoint meaning link differs from its exact observed value')
            facts.append(('endpoint', expression(row['meaning_link'], 'loop endpoint meaning')))
            state.conditions.append(operation('=', value, old))
        elif old != value:
            raise ValueError('The widened register does not match its declared binder')
        state.registers[register] = value
        if register in state.retained_registers:
            state.retained_registers[register] = value
    for relation in source['checked_cursor_relations']:
        if relation.get('kind') != 'affine_cursor':
            raise ValueError('The loop relation lacks an accepted renderer')
        for key in ['term', 'lower_bound', 'upper_bound']:
            facts.append(('cursor_' + key, expression(relation[key], 'loop cursor relation')))
    fold_renderings, required_imports = [], []
    fold_scope = {row['name']: row['type'] for row in rows}
    for resource in original_seed.resources:
        if resource.element_bits == 8 and resource.byte_array is not None and resource.byte_array.op == 'input':
            fold_scope[str(resource.byte_array.value)] = 'list (bv 8%N)'
    for relation in source['retained_fold_relations']:
        if fold_renderer is None:
            raise ValueError('A retained fold needs its exact source renderer')
        rendered_fold = fold_renderer(deepcopy(relation), scope=deepcopy(fold_scope))
        if (not isinstance(rendered_fold, dict) or set(rendered_fold) != {'term', 'imports'}
                or not isinstance(rendered_fold['imports'], list)):
            raise ValueError('The fold renderer returned an unsupported declaration interface')
        term = expression(rendered_fold['term'], 'retained fold proposition')
        for module in rendered_fold['imports']:
            identifier(module, 'fold import', qualified=True)
            if module not in required_imports:
                required_imports.append(module)
        facts.append(('retained_fold', term))
        fold_renderings.append({'relation': deepcopy(relation), 'scope': deepcopy(fold_scope),
                                'term': term, 'imports': list(rendered_fold['imports'])})
    for index, value in enumerate(projection['conditions']):
        # Expr.coq renders a boolean. State assumptions assert that it is true.
        facts.append(('source_condition_' + str(index),
                      '(' + Expr.from_dict(value).coq() + ') = true'))
    components = [item for item in components if item['id'] != terminal]
    tree['body']['children'] = [item for item in tree['body']['children']
                                if item != {'kind': 'component', 'id': terminal}]
    if any(terminal in str(item) for item in tree['body']['children']):
        raise ValueError('The inventory continuation has an unsupported nested scope')
    for index, (kind, term) in enumerate(facts):
        key = 'loop_fact_' + str(index)
        if any(item['id'] == key for item in components):
            raise ValueError('A loop relation captures an existing ownership identifier')
        components.append({'id': key, 'kind': 'opaque', 'source': '⌜' + term + '⌝',
            'scope': [[0]], 'provenance': {'kind': kind, 'source_index': source['source_index'],
                                         'minimal_conditions': deepcopy(source['minimal_condition_sets'])}})
        tree['body']['children'].append({'kind': 'component', 'id': key})
    # An inherited witness can disappear only when no emitted resource uses it.
    ownership['components'] = components
    image = apply_owned_writes(original_seed.resources, state.writes, conditions=state.conditions,
                              facts=original_seed.facts, endianness=state.endianness)
    probe = render_resource_boundary(ownership, image, state, vocabulary=vocabulary)
    if probe['block_status'] != 'completed':
        raise ValueError('The loop ownership image cannot render')
    text = ' '.join(item['source'] for item in probe['components'])
    removed = []
    for old in ownership['binders']:
        if re.search(r"(?<![\w'])" + re.escape(old['name']) + r"(?![\w'])", text):
            raise ValueError('An inherited loop witness needs an explicit selector input: ' + old['name'])
        removed.append({'kind': 'unused_source_binder', 'binder': deepcopy(old),
                        'reason': 'No emitted ownership component or loop fact uses this witness'})
    ordered = []
    for row in rows:
        record = {**deepcopy(row), 'scope': [0]}
        if row.get('register') is not None:
            record.update(value_key=row['register'], expression=state.registers[row['register']].to_dict())
        ordered.append(record)
    tree['binders'] = [{key: value for key, value in row.items() if key != 'scope'} for row in ordered]
    tree['scope'] = [0]
    for item in components:
        item['scope'] = [[0] if scope == [] else scope for scope in item.get('scope', [])]
    components.append({'id': terminal, 'kind': 'opaque', 'source': continuation['name'], 'scope': [],
        'provenance': {'contract_exit': deepcopy(continuation['source_binding'])}})
    ownership.update(components=components, binders=ordered, existential_prefixes=[],
        tree={'kind': 'sep', 'left': tree, 'right': {'kind': 'component', 'id': terminal}})
    seed = OwnedSeed(state, ownership, deepcopy(original_seed.resources), deepcopy(original_seed.facts), [],
        deepcopy(source['dropped_relation_records']) + omitted_conditions + removed,
        deepcopy(source['induction_checks']),
        deepcopy(source['loop_witness_plan']), 'loop_head')
    rendered = render_resource_boundary(ownership, image, state, vocabulary=vocabulary)
    if rendered['block_status'] != 'completed':
        raise ValueError('The assembled loop class cannot render its complete ownership')
    return {'seed': seed, 'boundary': rendered, 'removed_binders': removed,
        'required_imports': required_imports,
        'class_record': {'source_index': source['source_index'], 'seed': state.to_dict(),
            'binders': deepcopy(rows), 'relations': deepcopy(source['checked_cursor_relations']),
            'folds': deepcopy(source['retained_fold_relations']), 'edge_records': deepcopy(source['induction_checks']),
            'fold_renderings': fold_renderings, 'pending_fold_candidates': deepcopy(source.get('pending_fold_candidates', [])),
            'required_imports': list(required_imports),
            'refusals': deepcopy(seed.join_refusals), 'witness_plan': deepcopy(source['loop_witness_plan']),
            'body_results': deepcopy(source['body_results']),
            'control_transfer_obligations': deepcopy(source['control_transfer_obligations']),
            'zero_read_arm_refutation_source': deepcopy(source['zero_read_arm_refutation_source']),
            'minimal_condition_sets': deepcopy(source['minimal_condition_sets']),
            'inherited_source_facts': deepcopy(original_seed.facts),
            'source_fact_origin': 'Original public seed and source-domain facts; no trace-condition inference',
            'source_class_preserved': deepcopy(source),
            'kernel_entailments': 'OPEN'}}
