"""Prepare a source-preserving typed-array view. Do not initialize a state."""
from copy import deepcopy
import re

IDENTIFIER = r"[A-Za-z_][A-Za-z0-9_']*"
ARRAY = re.compile(r'(?P<base>.+?)\s*↦ₘ(?P<fraction>\{[^}]+\})?∗\s*\((?P<name>'+IDENTIFIER+r')\s*:\s*list\s*\(bv\s+8%N\)\s*\)\s*', re.S)


def adapt(seed):
    """Preserve propositions, binders, order, fractions, and unknown byte values."""
    result = deepcopy(seed)
    changes = []

    def visit(node, scope, path):
        if node['kind'] == 'sep':
            visit(node['left'], scope, path+'/left')
            visit(node['right'], scope, path+'/right')
        elif node['kind'] == 'exists':
            nested = dict(scope)
            for binder in node['binders']:
                if binder['name'] in nested:
                    raise ValueError('A shadowed binder requires an explicit scope identity.')
                nested[binder['name']] = binder['type']
            for index, child in enumerate(node['components']):
                visit(child, nested, path+'/components/'+str(index))
        elif node['kind'] == 'typed_array':
            source = node['coq']
            parsed = ARRAY.fullmatch(source.strip())
            if parsed is None:
                raise ValueError('The array source has no supported explicit byte-list ascription.')
            name = parsed['name']
            if re.sub(r'\s+', '', scope.get(name, '')) != 'list(bv8%N)':
                raise ValueError('The array value has no in-scope byte-list binder.')
            if parsed['fraction'] != '{'+node['fraction']+'}':
                raise ValueError('The array fraction differs from its source.')
            additions = {'kind': 'byte_array', 'original_component': source,
                         'original_address_z': parsed['base'].strip(),
                         'byte_array_expr': {'op': 'input', 'value': name},
                         'element_bits': 8, 'length_original_coq': 'List.length '+name}
            for key, value in additions.items():
                if key != 'kind' and key in node and node[key] != value:
                    raise ValueError('The existing source view conflicts with its typed array.')
            node.update(additions)
            changes.append({'pointer': path, 'original_coq': source, 'added_fields': sorted(set(additions)-{'kind'}),
                            'unknown_values_preserved': True, 'uninitialized_metadata_preserved': node.get('uninitialized', False)})
    visit(result['assertion_tree'], {}, '/assertion_tree')
    return result, changes
