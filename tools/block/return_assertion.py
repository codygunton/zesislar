"""Render an authenticated return assertion without assigning an entry status."""
from copy import deepcopy
from dataclasses import dataclass
import hashlib
import json

from render_support import expression, identifier


def _digest(value):
    return hashlib.sha256(json.dumps(value, sort_keys=True,
        separators=(',', ':')).encode()).hexdigest()


def _binders(rows):
    result = []
    for row in rows:
        result.append({'name': identifier(row['name'], 'return source binder'),
                       'type': expression(row['type'], 'return source type')})
    if len({row['name'] for row in result}) != len(result):
        raise ValueError('The return assertion repeats a scoped binder')
    return result


@dataclass
class ReturnAssertion:
    source: str | None
    manifest: dict
    reports: list


def format_return_assertion(resource, *, source_binding, pc, continuation_id,
                            guard_scope, condition_adapter, scoped_binders=()):
    """Keep the resource tree, its conditions, and its outer continuation exact.

    source_binding identifies the forward stop and its authenticated source file.
    guard_scope selects the existing existential that owns the path conditions.
    The caller supplies source-bound system binders, as for SymbolicConditions.
    This function renders declarations only. It does not classify a stop as an entry.
    """
    manifest = {'schema': 'source-return-assertion.v1',
                'source_binding': deepcopy(source_binding), 'pc': pc,
                'resource_sha256': _digest(resource),
                'guard_scope': list(guard_scope),
                'path_conditions': deepcopy(resource.get('path_conditions', [])),
                'ordered_writes': deepcopy(resource.get('write_accounting')),
                'original_tree': deepcopy(resource.get('tree')),
                'conditions': [], 'proof_ran': False}
    try:
        if not isinstance(source_binding, dict) or not all(
                source_binding.get(key) for key in ('path', 'sha256', 'pointer')):
            raise ValueError('The return assertion has no bound forward source')
        if resource.get('block_status') != 'completed' or resource.get('reports'):
            raise ValueError('The return resource accounting is incomplete')
        accounting = resource.get('write_accounting', {})
        if accounting.get('status') != 'complete':
            raise ValueError('The ordered source writes are incomplete')
        tree = resource['tree']
        if (tree.get('kind') != 'sep' or tree.get('right') !=
                {'kind': 'component', 'id': continuation_id}):
            raise ValueError('The return continuation has a different source scope')
        components = {row['id']: row for row in resource['components']}
        if len(components) != len(resource['components']):
            raise ValueError('The return resource identifiers repeat')
        extra = _binders(scoped_binders)
        seen, visits = set(), []

        def render(node, path, scope):
            kind = node['kind']
            local = _binders(node['binders']) if kind == 'exists' else []
            at_guard = tuple(path) == tuple(guard_scope)
            if at_guard:
                if kind != 'exists':
                    raise ValueError('The condition scope is not a source existential')
                visits.append(path)
                local = _binders(local + extra)
            nested = _binders(scope + local)
            if kind == 'component':
                key = node['id']
                if key in seen:
                    raise ValueError('The return tree repeats an owned component')
                seen.add(key)
                body = expression(components[key]['source'], 'source resource')
            elif kind == 'sep':
                body = '(' + render(node['left'], path + (0,), nested) + ' ∗ ' + \
                    render(node['right'], path + (1,), nested) + ')'
            elif kind == 'sep_list':
                children = node['children']
                if not children:
                    raise ValueError('The return tree has an empty resource list')
                body = '(' + ' ∗ '.join(render(child, path + (index,), nested)
                    for index, child in enumerate(children)) + ')'
            elif kind == 'exists':
                body = render(node['body'], path + (0,), nested)
            else:
                raise ValueError('The return assertion cannot preserve this node: ' + kind)
            if at_guard:
                for index, condition in enumerate(resource['path_conditions']):
                    context = {'pc': pc, 'alternative_index': 0,
                        'tree_path': list(path), 'condition_index': index,
                        'binders': deepcopy(nested),
                        'path_conditions': deepcopy(resource['path_conditions']),
                        'source_components': [{'id': row['id'], 'source': row['source']}
                            for row in resource['components']]}
                    lowered = condition_adapter(deepcopy(condition), context)
                    if set(lowered) != {'components', 'existentials'} or not lowered['components']:
                        raise ValueError('The return condition adapter omitted a condition')
                    local = _binders(local + _binders(lowered['existentials']))
                    nested = _binders(scope + local)
                    terms = []
                    for component in lowered['components']:
                        if component.get('kind') != 'pure' or not component.get('terms'):
                            raise ValueError('The return condition adapter changed a resource')
                        for term in component['terms']:
                            if not term.get('provenance'):
                                raise ValueError('The return condition has no source provenance')
                            terms.append(expression(term['term']['value'], 'return condition'))
                    body = '(' + body + ' ∗ ⌜' + ' /\\ '.join(
                        '(' + term + ')' for term in terms) + '⌝)'
                    manifest['conditions'].append({'index': index,
                        'source': deepcopy(condition), 'lowered': deepcopy(lowered)})
            if kind == 'exists':
                body = '(∃ ' + ' '.join('(' + row['name'] + ' : ' + row['type'] + ')'
                    for row in local) + ', ' + body + ')'
            return body

        result = render(tree, (), [])
        if len(visits) != 1:
            raise ValueError('The return condition scope does not occur exactly once')
        if seen != set(components):
            raise ValueError('The return tree omits a source resource')
        manifest['source_sha256'] = hashlib.sha256(result.encode()).hexdigest()
        return ReturnAssertion(result, manifest, [])
    except (KeyError, TypeError, ValueError) as error:
        return ReturnAssertion(None, manifest,
            [{'kind': 'return_assertion_stop', 'detail': str(error)}])
