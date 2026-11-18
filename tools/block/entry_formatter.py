"""Build existing author bodies from every source-derived forward alternative.

Adapters supply structured leaves and source-bound path terms. This module does
not parse successor entries, execute proofs, or select a preferred alternative.
"""
from copy import deepcopy
from dataclasses import dataclass
import hashlib
import json

try:
    from .entry_seed import _code_mask
    from .forward_resources import _strip_enclosure, parse_source_ownership
    from .symbolic_state import Expr, input_expr
    from .guard_normal_form import GuardNormalForm
    from .coq_scopes import z_address_scope
except ImportError:
    from entry_seed import _code_mask
    from forward_resources import _strip_enclosure, parse_source_ownership
    from symbolic_state import Expr, input_expr
    from guard_normal_form import GuardNormalForm
    from coq_scopes import z_address_scope


@dataclass
class FormattedEntry:
    response: dict | None
    manifest: dict
    reports: list

    @property
    def status(self):
        return 'complete' if self.response is not None else 'stopped'


def _digest(value):
    return hashlib.sha256(json.dumps(value, sort_keys=True, separators=(',', ':')).encode()).hexdigest()


def _binders(values):
    result = []
    for value in values:
        if not isinstance(value, dict) or not isinstance(value.get('name'), str) or not isinstance(value.get('type'), str):
            raise ValueError('A formatter binder needs a name and a type')
        result.append({'name': value['name'], 'type': value['type']})
    if len({value['name'] for value in result}) != len(result):
        raise ValueError('The formatter repeats an existential binder')
    return result


class SymbolicConditions:
    """Keep trace witnesses existential and missing source inputs explicit.

    provenance(context) supplies the existing typed author provenance record.
    aliases maps an exact source witness Expr to its source binder name.
    This adapter never introduces a binder for an unknown register or read.
    """

    def __init__(self, provenance, *, aliases=None, scalar_ranges=(), normal_form=True):
        self.provenance = provenance
        self.aliases = aliases or {}
        self.scalar_ranges = tuple(scalar_ranges)
        self.normal_form = normal_form
        self.witnesses = {}
        self.normalizations = []

    def __call__(self, expression, context):
        scope = {binder['name']: binder['type'] for binder in context['binders']}
        created = []

        def visit(value, introduce=True):
            if value in self.aliases:
                name = self.aliases[value]
                expected = 'bool' if value.width is None else f'bv {value.width}'
                if scope.get(name) != expected:
                    raise ValueError('A source witness has no matching scoped binder: ' + name)
                return input_expr(name, value.width)
            if value.op in {'unknown_input', 'unknown_read'}:
                raise ValueError('The condition has no source binding: ' + value.op)
            if value.op in {'local', 'write_result'}:
                identity = _digest(value.to_dict())
                name = 'forward_witness_' + identity[:16]
                kind = f'bv {value.width}' if value.width is not None else 'bool'
                if name in scope and scope[name] != kind:
                    raise ValueError('A trace witness has conflicting scoped types')
                if name not in scope and introduce:
                    created.append({'name': name, 'type': kind})
                    scope[name] = kind
                previous = self.witnesses.get(name)
                if previous is not None and previous != value.to_dict():
                    raise ValueError('Two trace witnesses have the same generated name')
                if introduce:
                    self.witnesses[name] = value.to_dict()
                return input_expr(name, value.width)
            return Expr(value.op, tuple(visit(arg, introduce) for arg in value.args), value.width, value.value)

        original = Expr.from_dict(expression)
        if original.width is not None:
            raise ValueError('A path condition has a bitvector value')
        lowered = visit(original)
        for row in self.scalar_ranges:
            if row.get('required_resource') not in context.get('source_components', []):
                raise ValueError('A scalar rewrite has no exact inherited source premise')
        term = lowered.coq() + ' = true'
        normalized = {'proposition': term, 'endpoints': [], 'rewrites': [], 'requirements': [], 'source_terms': []}
        if self.normal_form:
            path_conditions = [visit(Expr.from_dict(condition), introduce=False)
                               for condition in context.get('path_conditions', [expression])]
            normalizer = GuardNormalForm(path_conditions, scalar_ranges=self.scalar_ranges)
            normalized = normalizer.render(lowered)
        terms = list(dict.fromkeys([term, normalized['proposition'], *normalized['endpoints']]))
        provenance = self.provenance(deepcopy(context))
        if not isinstance(provenance, dict) or set(provenance) not in ({'source'}, {'from_block', 'from_instruction'}):
            raise ValueError('A condition needs source-bound author provenance')
        self.normalizations.append({'original_expression': deepcopy(expression),
            'lowered_expression': lowered.to_dict(), 'context': {key: deepcopy(value) for key, value in context.items()
                if key not in {'path_conditions', 'source_components'}},
            'original_term': term, **normalized})
        authored = [{'term': {'value': value}, 'provenance': provenance} for value in terms]
        authored.extend({'term': {'value': fact['term']}, 'provenance': {'source': fact['source']}}
                        for fact in normalized['source_terms'])
        return {'components': [{'kind': 'pure', 'terms': authored}], 'existentials': created}


class SourceComponents:
    """Lower source resource leaves without guessing opaque predicate owners.

    predicate_bindings maps an exact source name to an owner/name author record.
    provenance(record, context) supplies provenance for inherited pure terms.
    Explicit fractions stop here because the compact resource forms omit them.
    """

    def __init__(self, predicate_bindings, *, continuation_id, provenance):
        self.predicate_bindings = predicate_bindings
        self.continuation_id = continuation_id
        self.provenance = provenance

    def __call__(self, record, context):
        parsed = parse_source_ownership(record['source'], provenance=record.get('provenance', {}))
        if parsed['existential_prefixes']:
            raise ValueError('A source leaf contains an unrecorded existential scope')
        result = []
        for leaf in parsed['components']:
            kind = leaf['kind']
            if leaf.get('fraction') is not None:
                raise ValueError('The compact resource form cannot preserve an explicit fraction')
            if kind == 'register':
                result.append({'kind': kind, 'name': leaf['name'], 'value': leaf['value']})
            elif kind in {'byte_array', 'unknown_byte_array'}:
                key = 'value' if kind == 'byte_array' else 'length'
                result.append({'kind': kind, 'address': z_address_scope(leaf['address_z']), key: leaf[key]})
            else:
                source = _strip_enclosure(leaf['source'])
                if source == 'True':
                    result.append({'kind': 'true'})
                elif source.startswith('⌜') and source.endswith('⌝'):
                    result.append({'kind': 'pure', 'terms': [{'term': {'value': source[1:-1]},
                        'provenance': self.provenance(record, context)}]})
                elif source.startswith('reg_col '):
                    result.append({'kind': 'register_collection', 'value': source[len('reg_col '):].strip()})
                else:
                    parts, start, depth = [], 0, 0
                    mask = _code_mask(source, mask_strings=False)
                    quoted = False
                    for index, char in enumerate(mask):
                        if char == '"':
                            quoted = not quoted
                        elif quoted:
                            continue
                        elif char in '([{':
                            depth += 1
                        elif char in ')]}':
                            depth -= 1
                        elif char.isspace() and depth == 0:
                            if source[start:index].strip():
                                parts.append(source[start:index].strip())
                            start = index + 1
                    if source[start:].strip():
                        parts.append(source[start:].strip())
                    if not parts or parts[0] not in self.predicate_bindings:
                        raise ValueError('The opaque source predicate has no owner binding')
                    predicate = self.predicate_bindings[parts[0]]
                    if set(predicate) != {'owner', 'name'}:
                        raise ValueError('The source predicate binding is not a typed author reference')
                    result.append({'kind': 'continuation' if record['id'] == self.continuation_id else 'application',
                                   'predicate': deepcopy(predicate), 'arguments': parts[1:]})
        return result


def format_entry_boundary(boundary, *, case_id, source_policy, handwritten_owner,
                          continuation_id, guard_scope, component_adapter,
                          condition_adapter, helper_arguments, scoped_binders=(),
                          helper_parameter_order=None):
    """Return one inline answer with all alternatives and ordered helpers.

    component_adapter(record, context) returns ordered author components.
    condition_adapter(Expr_JSON, context) returns components and existentials.
    helper_arguments(body, context) returns arguments in the helper's order.
    Context carries pc, alternative_index, tree_path, and in-scope binders.

    guard_scope identifies the original existential node that owns conditions.
    scoped_binders adds source-bound system witnesses at that scope. Adapters must reject
    unavailable bindings. Any failure stops the complete answer, not a prefix.

    The inherited continuation must be the outer right operand in every tree.
    The formatter factors that identical operand outside the full disjunction.
    It keeps every other resource inside its original existential scope.
    """
    incoming = boundary.get('alternatives', [])
    alternatives = incoming
    if boundary.get('status') in {'generated_join', 'generated_loop_head'}:
        alternatives = [alternative for alternative in incoming
                        if alternative.get('predecessor_pc') is None
                        and alternative.get('seed_pc') == boundary.get('pc')]
    manifest = {'schema': 'entry-formatter-manifest.v1', 'pc': boundary.get('pc'),
                'alternative_count': len(alternatives), 'alternatives': [],
                'incoming_alternative_count': len(incoming) - len(alternatives),
                'helpers': [], 'continuation_id': continuation_id,
                'guard_scope': list(guard_scope), 'proof_ran': False}
    for index, alternative in enumerate(alternatives):
        resource = alternative.get('resource_boundary', {})
        manifest['alternatives'].append({'index': index, 'path': deepcopy(alternative.get('path')),
            'predecessor_pc': alternative.get('predecessor_pc'), 'seed_pc': alternative.get('seed_pc'),
            'resource_sha256': _digest(resource),
            'path_conditions': deepcopy(resource.get('path_conditions', [])),
            'tree': deepcopy(resource.get('tree'))})
    reports, definitions, choices = [], [], []
    exact_alternatives = []
    manifest['exact_duplicate_alternatives'] = []
    active = {'alternative_index': None, 'tree_path': []}
    try:
        if boundary.get('status') not in {'generated', 'generated_join', 'generated_loop_head'} or not alternatives:
            raise ValueError('The boundary has no generated alternatives')
        if not guard_scope:
            raise ValueError('Conditions require an explicit existential source scope')
        if helper_parameter_order not in (None, 'free_source_order'):
            raise ValueError('The helper parameter order is unsupported')
        extra_binders = _binders(scoped_binders)
        common_continuation = None
        for alternative_index, alternative in enumerate(alternatives):
            definition_start = len(definitions)
            helper_start = len(manifest['helpers'])
            resource = alternative['resource_boundary']
            if resource.get('block_status') != 'completed':
                raise ValueError('An alternative has incomplete resource accounting')
            tree = resource['tree']
            if (tree.get('kind') != 'sep' or
                    tree.get('right') != {'kind': 'component', 'id': continuation_id}):
                raise ValueError('The caller continuation has a different source scope')
            components = {record['id']: record for record in resource['components']}
            if len(components) != len(resource['components']):
                raise ValueError('An alternative repeats a resource identifier')
            continuation = components[continuation_id]
            if common_continuation is None:
                common_continuation = continuation
            elif continuation != common_continuation:
                raise ValueError('The inherited caller continuation differs between alternatives')
            seen, guard_visits = set(), []

            def context(path, scope):
                active.update(alternative_index=alternative_index, tree_path=list(path))
                return {'pc': boundary['pc'], 'alternative_index': alternative_index,
                        'tree_path': list(path), 'binders': deepcopy(scope)}

            def declaration(body, path, outer_scope):
                if helper_parameter_order is not None:
                    body['parameter_order'] = helper_parameter_order
                suffix = f'ForwardA{alternative_index}N{len(definitions)}'
                reference = {'suffix': suffix}
                ctx = context(path, outer_scope)
                arguments = helper_arguments(deepcopy(body), ctx)
                if not isinstance(arguments, list):
                    raise ValueError('The helper arguments must be an ordered list')
                definitions.append({'position': 'before', 'role': 'entry_variant', 'suffix': suffix,
                                    'handwritten_owner': handwritten_owner, 'body': body})
                manifest['helpers'].append({'suffix': suffix, 'alternative_index': alternative_index,
                    'tree_path': list(path), 'outer_binders': deepcopy(outer_scope),
                    'arguments': deepcopy(arguments), 'body_sha256': _digest(body)})
                return {'kind': 'application', 'predicate': reference, 'arguments': arguments}

            def compile_node(node, path, scope):
                kind = node['kind']
                ctx = context(path, scope)
                local = _binders(node['binders']) if kind == 'exists' else []
                at_guard = tuple(path) == tuple(guard_scope)
                if at_guard:
                    guard_visits.append(path)
                    if kind != 'exists' and guard_scope:
                        raise ValueError('The condition scope does not select an existential node')
                    local = _binders(local + extra_binders)
                nested_scope = scope + local
                if len({item['name'] for item in nested_scope}) != len(nested_scope):
                    raise ValueError('A source existential shadows an outer formatter binder')
                if kind == 'component':
                    resource_id = node['id']
                    if resource_id == continuation_id or resource_id in seen:
                        raise ValueError('The source tree repeats an owned component')
                    seen.add(resource_id)
                    authored = component_adapter(deepcopy(components[resource_id]), ctx)
                elif kind == 'sep':
                    authored = (compile_node(node['left'], path+(0,), nested_scope) +
                                compile_node(node['right'], path+(1,), nested_scope))
                elif kind == 'sep_list':
                    authored = []
                    for index, child in enumerate(node['children']):
                        authored.extend(compile_node(child, path+(index,), nested_scope))
                elif kind == 'exists':
                    authored = compile_node(node['body'], path+(0,), nested_scope)
                else:
                    raise ValueError('The formatter cannot preserve this assertion node: ' + kind)
                if not isinstance(authored, list) or not authored:
                    raise ValueError('A resource adapter returned no structured components')
                if at_guard:
                    for condition_index, condition in enumerate(resource['path_conditions']):
                        condition_context = context(path, nested_scope)
                        condition_context['condition_index'] = condition_index
                        condition_context['path_conditions'] = deepcopy(resource['path_conditions'])
                        condition_context['source_components'] = [
                            {'id': item['id'], 'source': item['source']} for item in resource['components']]
                        lowered = condition_adapter(deepcopy(condition), condition_context)
                        if set(lowered) != {'components', 'existentials'} or not lowered['components']:
                            raise ValueError('A condition adapter did not preserve a condition')
                        new_binders = _binders(lowered['existentials'])
                        local = _binders(local + new_binders)
                        nested_scope = scope + local
                        if len({item['name'] for item in nested_scope}) != len(nested_scope):
                            raise ValueError('A condition witness shadows an outer binder')
                        authored.extend(lowered['components'])
                if kind == 'exists':
                    body = {'components': authored, 'source_policy': source_policy,
                            'existentials': local, 'lets': [], 'loop': None,
                            'continuation': {'mode': 'none'}}
                    return [declaration(body, path, scope)]
                return authored

            left = compile_node(tree['left'], (0,), [])
            if len(guard_visits) != 1:
                raise ValueError('The condition scope does not occur exactly once')
            if seen | {continuation_id} != set(components):
                raise ValueError('The assertion tree omits a source resource')
            if len(left) == 1 and left[0]['kind'] == 'application':
                choice = left[0]
            else:
                body = {'components': left, 'source_policy': source_policy, 'existentials': [],
                        'lets': [], 'loop': None, 'continuation': {'mode': 'none'}}
                choice = declaration(body, (0,), [])
            # Validate and render every input before considering exact equality.
            # Missing rendered source text retains the existing alternatives.
            source_body = resource.get('body')
            exact_key = None
            if isinstance(source_body, str):
                guards = json.dumps(resource['path_conditions'], ensure_ascii=False,
                                    separators=(',', ':'))
                authored = _digest({
                    'bodies': [row['body'] for row in definitions[definition_start:]],
                    'signatures': [{key: row[key] for key in
                        ['tree_path', 'outer_binders', 'arguments']}
                        for row in manifest['helpers'][helper_start:]],
                })
                exact_key = (source_body, guards, continuation['source'], authored)
            exact_alternatives.append({
                'key': exact_key, 'definition_end': len(definitions),
                'helper_end': len(manifest['helpers']),
                'alternative_index': alternative_index,
            })
            choices.append(choice)
        continuation = component_adapter(deepcopy(common_continuation),
            {'pc': boundary['pc'], 'alternative_index': None, 'tree_path': [1], 'binders': []})
        if len(continuation) != 1 or continuation[0].get('kind') != 'continuation':
            raise ValueError('The caller adapter must return one continuation component')
        first_exact = exact_alternatives[0]
        identical = (first_exact['key'] is not None and
                     all(row['key'] == first_exact['key'] for row in exact_alternatives))
        manifest['exact_deduplication'] = {
            'all_rendered_resources_available': all(row['key'] is not None for row in exact_alternatives),
            'all_alternatives_byte_identical': identical,
        }
        if len(choices) > 1 and identical:
            source_body, guards, caller, _ = first_exact['key']
            manifest['exact_duplicate_alternatives'] = [{
                'alternative_index': row['alternative_index'],
                'canonical_alternative_index': first_exact['alternative_index'],
                'rendered_resources_sha256': hashlib.sha256(source_body.encode()).hexdigest(),
                'guards_sha256': hashlib.sha256(guards.encode()).hexdigest(),
                'continuation_sha256': hashlib.sha256(caller.encode()).hexdigest(),
            } for row in exact_alternatives[1:]]
            del definitions[first_exact['definition_end']:]
            del manifest['helpers'][first_exact['helper_end']:]
            choices = choices[:1]
        choice = choices[0] if len(choices) == 1 else {'kind': 'disjunction', 'alternatives': choices}
        manifest['emitted_alternative_count'] = len(choices)
        body = {'at': boundary['pc'], 'components': [choice, continuation[0]], 'existentials': [],
                'lets': [], 'loop': None,
                'continuation': {'mode': 'from_resource_component', 'resource_component': 1,
                                 'placement': 'explicit', 'order': 'resources_first'},
                'additional_definitions': definitions}
        response = {'schema': 'entry-pilot.inline-body.v1', 'case_id': case_id, 'body': body}
        manifest['response_sha256'] = _digest(response)
        return FormattedEntry(response, manifest, reports)
    except (ValueError, KeyError, TypeError) as error:
        reports.append({'kind': 'entry_formatter_stop', **active, 'detail': str(error)})
        return FormattedEntry(None, manifest, reports)


def format_owned_entry_boundary(boundary, *, original_seed, vocabulary, continuation,
                                continuation_id, join_options=None, **options):
    """Deduplicate first, then generalize every remaining multi-alternative cut.

    The caller supplies the original owned seed and the source-bound outer
    continuation. Exact formatting checks run before generalization. A refused
    join returns no declaration, rather than retaining a path disjunction.
    """
    try:
        from .join_generalize import generalize_owned_join
    except ImportError:
        from join_generalize import generalize_owned_join

    def framed(source):
        value = deepcopy(source)
        if value.get('status') == 'handwritten_cut':
            value['status'] = 'generated'
        for alternative in value.get('alternatives', []):
            resource = alternative['resource_boundary']
            if any(row['id'] == continuation_id for row in resource['components']):
                raise ValueError('The outer continuation captures an owned resource')
            resource['tree'] = {'kind': 'sep', 'left': resource['tree'],
                                'right': {'kind': 'component', 'id': continuation_id}}
            resource['components'].append({'id': continuation_id, 'source': continuation['name'],
                                          'provenance': deepcopy(continuation['source_binding'])})
        return value

    try:
        if (not isinstance(continuation, dict) or
                set(continuation) != {'name', 'coq', 'source_binding', 'terminal_id'} or
                not continuation['source_binding']):
            raise ValueError('An entry cut needs a source-bound outer continuation')
        first = format_entry_boundary(framed(boundary), continuation_id=continuation_id, **options)
        if first.response is None:
            return first
        if first.manifest['emitted_alternative_count'] <= 1:
            first.manifest['cut_generalization'] = {
                'kind': 'exact_deduplication' if first.manifest['exact_duplicate_alternatives']
                        else 'single_alternative', 'proof_established': False}
            return first
        joined = generalize_owned_join(boundary['alternatives'], original_seed=original_seed,
            entry_pc=int(boundary['pc'], 0), vocabulary=vocabulary, continuation=continuation,
            **(join_options or {}))
        if joined['plan']['join_refusals']:
            raise ValueError('The cut needs an unsupported guard hull: ' +
                             json.dumps(joined['plan']['join_refusals'], sort_keys=True))
        generalized = deepcopy(joined['boundary'])
        for alternative in generalized['alternatives']:
            resource = alternative['resource_boundary']
            terminal = continuation['terminal_id']
            if resource['tree']['right'] != {'kind': 'component', 'id': terminal}:
                raise ValueError('The generalized continuation has another source scope')
            resource['tree']['right']['id'] = continuation_id
            records = [row for row in resource['components'] if row['id'] == terminal]
            if len(records) != 1 or records[0]['source'] != continuation['name']:
                raise ValueError('The generalized continuation has another owned value')
            records[0]['id'] = continuation_id
        result = format_entry_boundary(generalized, continuation_id=continuation_id, **options)
        result.manifest['cut_generalization'] = {
            'kind': 'generalized_owned_cut', 'original_alternative_count': len(boundary['alternatives']),
            'deduplication': first.manifest['exact_deduplication'], 'plan': joined['plan'],
            'proof_established': False}
        return result
    except (ValueError, KeyError, TypeError) as error:
        return FormattedEntry(None, {'schema': 'entry-formatter-manifest.v1',
            'pc': boundary.get('pc'), 'proof_ran': False},
            [{'kind': 'entry_cut_generalization_stop', 'detail': str(error)}])
