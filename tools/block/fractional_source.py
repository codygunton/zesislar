"""Preserve explicit array fractions with the source-bound helper signature."""
from copy import deepcopy
import hashlib
from pathlib import Path

try:
    from .forward_resources import parse_source_ownership
    from .coq_scopes import z_address_scope
except ImportError:
    from forward_resources import parse_source_ownership
    from coq_scopes import z_address_scope


def array_declaration(vocabulary):
    """Select the exact reviewed array declaration and verify its source."""
    rows = [row for row in vocabulary['rows'] if row.get('kind') == 'owned_byte_array']
    if len(rows) != 1:
        raise ValueError('The source vocabulary has no unique owned-array declaration')
    helper = deepcopy(rows[0]['helper'])
    if helper['arguments'] != ['implicit n : N', 'a : Z', 'q : dfrac', 'l : list (bv n)']:
        raise ValueError('The array helper has an unsupported argument order')
    source = helper['source']
    if hashlib.sha256(Path(source['path']).read_bytes()).hexdigest() != source['sha256']:
        raise ValueError('The bound array declaration source changed')
    if helper['name'] != source['declaration'] or helper['name'] != 'mem_mapsto_array_def':
        raise ValueError('The array helper differs from its bound declaration')
    helper['vocabulary_sha256'] = vocabulary['input_sha256']
    return helper


class FractionalSourceArrays:
    """Adapt explicit array fractions. Preserve all other source leaves.

    The source equality between the sealed array and its definition remains a
    checker obligation. This adapter renders declarations and runs no proof.
    """

    def __init__(self, plain_adapter, *, declaration):
        self.plain_adapter = plain_adapter
        self.declaration = deepcopy(declaration)
        if declaration['arguments'] != ['implicit n : N', 'a : Z', 'q : dfrac', 'l : list (bv n)']:
            raise ValueError('The array helper has an unsupported argument order')
        self.applications = []

    def __call__(self, record, context):
        parsed = parse_source_ownership(record['source'], provenance=record.get('provenance', {}))
        if parsed['existential_prefixes']:
            raise ValueError('A source leaf contains an unrecorded existential scope')
        result = []
        for leaf in parsed['components']:
            fraction = leaf.get('fraction')
            if fraction is None:
                result.extend(self.plain_adapter({**record, 'source': leaf['source']}, context))
                continue
            if leaf['kind'] != 'byte_array':
                raise ValueError('The source-bound array adapter cannot preserve this fractional resource')
            arguments = [z_address_scope(leaf['address_z']), '(' + fraction[1:-1] + ')', leaf['value']]
            result.append({'kind': 'application', 'predicate': {
                'owner': self.declaration['owner'], 'name': self.declaration['name']},
                'arguments': arguments})
            self.applications.append({'resource_id': record['id'], 'context': deepcopy(context),
                'original_source': leaf['source'], 'fraction': fraction,
                'arguments': deepcopy(arguments), 'declaration': deepcopy(self.declaration),
                'required_source_equality': self.declaration['owner'] + '.mem_mapsto_array_eq',
                'proof_checked': False})
        return result
