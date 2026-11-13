"""Reconstruct a whole owned array from per-edge source write images."""
try:
    from .forward_resources import _memory_source, parse_source_ownership
    from .join_affine import affine_eliminate
    from .symbolic_state import MemoryWrite, bits, operation
except ImportError:
    from forward_resources import _memory_source, parse_source_ownership
    from join_affine import affine_eliminate
    from symbolic_state import MemoryWrite, bits, operation


def affine_memory_image(resource, paths, *, basis, expressions, register_names, vocabulary):
    """Accept only an identical store layout on every authenticated source edge.

    paths contains (MemoryWrite, offset) pairs from complete ownership results.
    A field that cannot use the existing register inputs refuses. This helper
    introduces no memory input constructor or independent memory witness.
    """
    # The caller asks only when the edges state the array differently. With no store on any
    # edge, the difference comes from the edges' seeds, which no store layout reconstructs.
    if not any(paths) or resource.byte_array is None or resource.element_bits != 8:
        return {'status': 'refused', 'kind': 'join_memory_refusal', 'detail': 'The array needs explicit packaging'}
    if any(type(offset) is not int for path in paths for _, offset in path):
        return {'status': 'refused', 'kind': 'join_memory_refusal', 'detail': 'A store has a symbolic offset'}
    layout = [(offset, write.size) for write, offset in paths[0]]
    if any([(offset, write.size) for write, offset in path] != layout for path in paths):
        return {'status': 'refused', 'kind': 'join_memory_refusal', 'detail': 'The source store layouts differ'}
    length = resource.length.value if hasattr(resource.length, 'op') and resource.length.op == 'bits' else resource.length
    for path in paths:
        for write, offset in path:
            if (write.ownership_id != resource.id or write.mapped is not True or type(offset) is not int
                    or offset < 0 or write.size not in (1, 2, 4, 8) or write.value.width != write.size * 8):
                raise ValueError('A join store lacks a typed source owner')
            if type(length) is not int or offset + write.size > length:
                return {'status': 'refused', 'kind': 'join_memory_refusal', 'detail': 'The complete array extent is unavailable'}
    stores, relations, updates = [], [], {}
    for index, (offset, size) in enumerate(layout):
        values = [path[index][0].value for path in paths]
        if all(value == values[0] for value in values[1:]):
            value = values[0]
        else:
            compatible = {name: rows for name, rows in basis.items()
                          if expressions[name].width == size * 8}
            solved = affine_eliminate(values, compatible, expressions={name: expressions[name] for name in compatible},
                                       register_names=[name for name in register_names if name in compatible])
            if solved['status'] != 'generated':
                return {'status': 'refused', 'kind': 'join_memory_refusal', 'offset': offset,
                        'detail': 'The field needs an unavailable memory witness', 'affine_refusal': solved}
            try:
                from .symbolic_state import Expr
            except ImportError:
                from symbolic_state import Expr
            value = Expr.from_dict(solved['expression'])
            relations.append({'offset': offset, 'size': size, 'solution': solved,
                              'source_values': [item.to_dict() for item in values]})
        write = MemoryWrite(operation('bvadd', resource.base, bits(offset, resource.base.width)), value, size, True,
                            provenance={'kind': 'join_source_reconstruction',
                                        'source_events': [path[index][0].provenance for path in paths]},
                            ownership_id=resource.id)
        stores.append((write, offset))
        for byte in range(size):
            updates[offset + byte] = {'value': operation('extract', value, width=8, value=byte * 8).to_dict()}
    source = _memory_source(resource, updates, stores, {}, vocabulary)
    parsed, = parse_source_ownership(source, provenance=resource.provenance)['components']
    if parsed['kind'] != 'byte_array':
        raise ValueError('The join reconstruction lost whole-array ownership')
    return {'status': 'generated', 'resource_id': resource.id, 'source': source, 'value': parsed['value'],
            'updates': updates, 'relations': relations, 'edge_count': len(paths), 'proof_established': False}
