"""Render ownership provenance from a bound join seed, never its conclusion."""
from copy import deepcopy
import hashlib
from pathlib import Path

try:
    from .check_data_only_lemmas import atom, rocq_tokens
    from .render_support import binders, expression, identifier
except ImportError:
    from check_data_only_lemmas import atom, rocq_tokens
    from render_support import binders, expression, identifier


def ownership_source(join, *, source_name, target_name, parameters, imports, source_evidence):
    """Return a source-only owner with explicit register parameters and all edges."""
    identifier(source_name, 'join source owner')
    identifier(target_name, 'join target')
    if source_name == target_name:
        raise ValueError('The target cannot supply its own witness provenance')
    seed = join['seed']
    alternatives = join['boundary']['alternatives']
    if len(alternatives) != 1 or alternatives[0].get('predecessor_pc') is not None:
        raise ValueError('An ownership source needs one generated seed')
    boundary = alternatives[0]['resource_boundary']
    if boundary.get('block_status') != 'completed':
        raise ValueError('An ownership source has incomplete resources')
    components = {row['id']: row for row in boundary['components']}
    owned = seed.ownership['components']
    if len(components) != len(boundary['components']) or set(components) != {row['id'] for row in owned}:
        raise ValueError('The rendered ownership components differ from the bound seed')
    if not source_evidence:
        raise ValueError('An ownership source needs its bound input evidence')
    for binding in source_evidence:
        data = Path(binding['path']).read_bytes()
        if hashlib.sha256(data).hexdigest() != binding['sha256']:
            raise ValueError('The join ownership source evidence changed')
    outer = {name for name, _ in binders(parameters, ['Sigma'])}
    register_binders = []
    for binder in seed.ownership.get('binders', []):
        if (not binder.get('value_key') or binder['expression'].get('op') != 'input'
                or binder['expression'].get('value') != binder['name']
                or binder['type'].split()[:1] != ['bv']):
            raise ValueError('A source witness needs an explicit owned register parameter')
        register_binders.append({'name': binder['name'], 'type': binder['type']})
    typed_binders = binders(register_binders, outer | {'Sigma'})
    names = [name for name, _ in typed_binders]
    if seed.join_witness_plan.get('ordered_binders') != names:
        raise ValueError('The source register parameters differ from witness declaration order')
    edges = seed.join_edges
    if not edges or len({row['index'] for row in edges}) != len(edges):
        raise ValueError('An ownership source needs complete distinct edge records')
    for row in edges:
        if (not {'predecessor_pc', 'path', 'ordered_witnesses', 'original_values',
                 'original_conditions', 'certificate'} <= row.keys()
                or [value['binder'] for value in row['ordered_witnesses']] != names):
            raise ValueError('A join edge lacks its complete witness provenance')
    continuation = join['continuation']['terminal_id']
    sources, retained, excluded, fragments = [], [], [], []
    for row in owned:
        rendered = components[row['id']]
        tokens = [token for token, _ in rocq_tokens(rendered['source'])]
        if row['id'] == continuation or row['kind'] == 'pure' or tokens[:1] == ['⌜']:
            excluded.append(row['id'])
            continue
        if row['kind'] not in {'register', 'byte_array', 'unknown_byte_array', 'opaque'}:
            raise ValueError('A source ownership component has an unsupported shape')
        source = rendered['source']
        if row['kind'] in {'byte_array', 'unknown_byte_array'}:
            lexed = rocq_tokens(source)
            markers = [position for position in range(len(lexed) - 1)
                       if [token for token, _ in lexed[position:position + 2]] == ['↦', 'ₘ']]
            if len(markers) != 1:
                raise ValueError('The source array needs one exact ownership address')
            start = lexed[markers[0]][1]
            address, suffix = source[:start].strip(), source[start:]
            words = [token for token, _ in rocq_tokens(address)]
            if not words:
                raise ValueError('The source array has no address')
            if words[0] != '(' or atom(words, 0)[1] != len(words):
                source = '(' + address + ') ' + suffix
            # This groups a term in the new declaration. It preserves the exact
            # source fraction and array payload. No existing file is rewritten.
            assert source[source.index('↦'): ] == suffix
        sources.append(expression(source, 'join ownership resource'))
        fragments.append({'id': row['id'], 'original': rendered['source'], 'emitted': source})
        retained.append(row['id'])
    if not sources:
        raise ValueError('The join seed has no ownership resources')
    if not imports or imports[0] != 'ZesuSsz.Automation.All':
        raise ValueError('The source owner must start with the standard automation import')
    for module in imports:
        identifier(module, 'source owner import', qualified=True)
    header = ''.join('Require Import ' + module + '.\n' for module in dict.fromkeys(
        [imports[0], 'isla.riscv64.riscv64', 'Coq.Lists.List', *imports[1:]]))
    header += 'Import ListNotations.\nOpen Scope Z_scope.\n'
    typed = ''.join(' (' + name + ' : ' + kind + ')' for name, kind in
                    [*binders(parameters, ['Sigma']), *typed_binders])
    body = '(' + ' ∗ '.join([*sources, 'True']) + ')%I'
    text = (header + 'Definition ' + source_name + ' `{!islaG Sigma} `{!threadG}'
            + typed + ' : iProp Sigma :=\n  ' + body + '.\n')
    return {'source': text, 'declaration': source_name,
            'parameters': deepcopy(parameters) + register_binders,
            'retained_components': retained, 'excluded_nonownership': excluded,
            'source_fragments': fragments,
            'source_evidence': deepcopy(source_evidence), 'edges': deepcopy(edges),
            'witness_plan': deepcopy(seed.join_witness_plan), 'proof_established': False}
