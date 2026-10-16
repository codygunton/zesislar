"""Validate schema2 catalog references without expanding complete contexts."""
from collections.abc import Mapping, Sequence


def _array(value):
    return isinstance(value, Sequence) and not isinstance(value, (str, bytes))


def selected_ids(groups):
    """Keep raw groups unchanged and return their sorted identity union."""
    values = []
    for name in ('goals', 'shelf', 'given_up'):
        rows = groups[name]
        if not _array(rows):
            raise ValueError('The compact catalog lacks its raw group identities.')
        for key in rows:
            if type(key) is not int or key < 0:
                raise ValueError('A compact selected identity is invalid.')
            values.append(key)
    return sorted(set(values))


def catalog_header(catalog, sidecar, groups):
    """Require exact historical fields or the source-bound compact contract."""
    from trace_block_kernel_display import _exact
    version = catalog.get('schema')
    if type(version) is not int or version not in (1, 2):
        raise ValueError('The evar catalog schema is unsupported.')
    expected = {'schema', 'complete_sidecar', 'entries'}
    if version == 2:
        expected.add('selected_ids')
    if set(catalog) != expected or not _exact(catalog['complete_sidecar'], sidecar):
        raise ValueError('The evar catalog has different fields or sidecar.')
    if not _array(catalog['entries']):
        raise ValueError('The complete evar catalog lacks ordered entries.')
    if version == 2:
        ids = catalog['selected_ids']
        if (not _array(ids) or any(type(key) is not int or key < 0 for key in ids)
                or list(ids) != selected_ids(groups)):
            raise ValueError('The compact catalog differs from its exact selected identities.')
    return version


def descriptor(value, sidecar, index, evar, field, count):
    """Bind one nonselected field to its exact complete Marshal entry."""
    from trace_block_kernel_display import _exact
    if type(count) is not int or count < 0:
        raise ValueError('A compact catalog count is invalid.')
    expected = {'availability': 'referenced', 'complete_sidecar': sidecar,
                'catalog_index': index, 'evar': evar, 'field': field, 'count': count}
    if (not isinstance(value, Mapping) or set(value) != set(expected)
            or any(type(value[key]) is not int for key in ('catalog_index', 'evar', 'count'))
            or any(not _exact(value[key], item) for key, item in expected.items())):
        raise ValueError('A compact field differs from its exact catalog association.')


def receipt_check(value, catalog):
    """Require the pinned reader's complete compact-to-Marshal comparison."""
    from trace_block_kernel_display import _exact
    count = len(catalog['entries']) - len(catalog['selected_ids'])
    expected = {'schema': 2, 'entries': len(catalog['entries']),
                'selected_ids': catalog['selected_ids'],
                'referenced_contexts': count, 'referenced_filters': count,
                'complete': True, 'verification': 'compact-catalog-to-Marshal'}
    if (count < 0 or not isinstance(value, Mapping) or set(value) != set(expected)
            or any(type(value[key]) is not int for key in
                   ('schema', 'entries', 'referenced_contexts', 'referenced_filters'))
            or value['complete'] is not True
            or any(not _exact(value[key], item) for key, item in expected.items())):
        raise ValueError('The compact catalog lacks its complete reader receipt.')
