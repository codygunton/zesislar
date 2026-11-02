"""Bind an explicit public assertion tree to values and inherited ownership."""
from dataclasses import dataclass
import hashlib
import json
from pathlib import Path
import re

from forward_resources import (OwnedBytes, _strip_enclosure, _top_positions,
                               ownership_from_assertion_tree)
from symbolic_state import Expr, MemoryRegion, SymbolicState, bits, input_expr, operation


def load_public_seed(path, expected_sha256):
    data = Path(path).read_bytes()
    if hashlib.sha256(data).hexdigest() != expected_sha256:
        raise ValueError('The public seed hash differs from its boundary')
    seed = json.loads(data)
    if seed.get('schema') != 'h1-public-entry-seed.v1':
        raise ValueError('The public seed schema is unsupported')
    for source in seed['source_bindings']:
        if hashlib.sha256(Path(source['path']).read_bytes()).hexdigest() != source['sha256']:
            raise ValueError('A public seed source changed')
    seed['_input_sha256'] = expected_sha256
    return seed


@dataclass
class DomainFacts:
    constants: dict
    facts: list
    source_packet: dict


def load_domain_facts(path, expected_sha256):
    """Adapt typed source facts without removing their original propositions."""
    data = Path(path).read_bytes()
    if hashlib.sha256(data).hexdigest() != expected_sha256:
        raise ValueError('The domain fact hash differs from its boundary')
    packet = json.loads(data)
    sources, checked = {source['id']: source for source in packet['sources']}, {}
    for source in sources.values():
        name = source['path']
        if name not in checked:
            checked[name] = hashlib.sha256(Path(name).read_bytes()).hexdigest()
        if checked[name] != source['sha256']:
            raise ValueError('A domain fact source changed')
    facts = []
    for original in packet['facts']:
        fact = {**original, 'terms': dict(original['terms']), 'origin': dict(original['origin'])}
        fact['origin']['source_bindings'] = [sources[name] for name in fact['origin'].get('source_ids', [])]
        if fact['status'] == 'derived-by-source-arithmetic':
            fact['original_status'] = fact['status']
            fact['status'] = 'derived-by-pass'
        terms = fact['terms']
        if fact['kind'] == 'disjoint_ranges':
            terms.update(left=terms['left_resource'], right=terms['right_resource'])
        if fact['kind'] == 'permission' and isinstance(terms.get('fraction'), dict):
            terms['fraction_typed'] = terms['fraction']
            terms['fraction'] = terms['fraction_typed']['original_coq']
        facts.append(fact)
    constants = {row['original_coq']: {'value': row['value'], 'type': row['type'],
                  'origin': {'packet_sha256': expected_sha256, 'source_id': row.get('source_id'),
                             'fact_id': row.get('fact_id')}} for row in packet['scalar_constants']}
    for fact in facts:
        terms = fact['terms']
        if fact['kind'] != 'bounds' or terms.get('relation') != '=':
            continue
        for length, view in ((terms.get('left'), terms.get('right')), (terms.get('right'), terms.get('left'))):
            if not isinstance(length, dict) or not isinstance(view, dict):
                continue
            original = length.get('original_coq', '')
            if original.startswith('Z.of_nat ') and _length_key(original[len('Z.of_nat '):]).startswith('length '):
                terms['resource_id'] = length['resource_id']
                terms['length_view'] = source_z_expression(view['original_coq'], constants).to_dict()
    return DomainFacts(constants, facts, packet)


def _constant(term, constants):
    term = _strip_enclosure(re.sub(r'%(?:Z|nat|N)\s*$', '', term.strip()))
    if re.fullmatch(r'-?[0-9]+', term):
        return int(term)
    if term in constants:
        binding = constants[term]
        if not isinstance(binding, dict) or type(binding.get('value')) is not int or not binding.get('origin'):
            raise ValueError('A scalar constant needs its exact value and source origin')
        return binding['value']
    return None


def load_scalar_constants(source_bindings, names):
    """Read requested closed integer declarations from bound source files."""
    result, sources = {}, {}
    for binding in source_bindings:
        path = binding['path']
        if path not in sources:
            data = Path(path).read_bytes()
            if hashlib.sha256(data).hexdigest() != binding['sha256']:
                raise ValueError('A scalar constant source changed')
            sources[path] = data.decode()
        for name in names:
            pattern = (r'\bDefinition\s+' + re.escape(name) +
                       r'\s*:\s*(Z|nat|N)\s*:=\s*(-?[0-9]+)(?:%(?:Z|nat|N))?\s*\.')
            for match in re.finditer(pattern, sources[path]):
                value = {'value': int(match[2]), 'type': match[1],
                         'origin': {'path': path, 'sha256': binding['sha256'], 'declaration': name}}
                if name in result and result[name]['value'] != value['value']:
                    raise ValueError('Two source declarations disagree on a scalar constant')
                result[name] = value
    return result


def source_z_expression(term, constants, width=64):
    """Translate source Z addition and subtraction under a bitvector cast."""
    term = _strip_enclosure(re.sub(r'%Z\s*$', '', term.strip()))
    value = _constant(term, constants)
    if value is not None:
        return bits(value, width)
    operators = [position for operator in ('+', '-') for position in _top_positions(term, operator)
                 if position > 0 and not term.startswith('->', position)]
    if operators:
        position = max(operators)
        return operation('bvadd' if term[position] == '+' else 'bvsub',
                         source_z_expression(term[:position], constants, width),
                         source_z_expression(term[position+1:], constants, width))
    return input_expr(f'(Z_to_bv {width}%N ({term}))', width)


def source_bv_expression(term, constants, width=64):
    term = _strip_enclosure(term)
    cast = re.fullmatch(r'Z_to_bv\s+([0-9]+)(?:%N)?\s+(.+)', term, re.S)
    if cast:
        if int(cast[1]) != width:
            raise ValueError('The source bitvector width differs')
        return source_z_expression(cast[2], constants, width)
    return input_expr(term, width)


def _length_key(term):
    term = _strip_enclosure(term)
    term = re.sub(r'(?:Coq\.Lists\.List\.|List\.)?length\b', 'length', term)
    return ' '.join(term.split())


def _source_lengths(ownership, constants):
    lengths = {}
    for component in ownership['components']:
        for statement in component['seed_component'].get('well_formed_facts', []):
            statement = _strip_enclosure(re.sub(r'%nat\s*$', '', statement.strip()))
            equalities = list(_top_positions(statement, '='))
            if len(equalities) != 1:
                continue
            at = equalities[0]
            for term, value in ((statement[:at], statement[at+1:]), (statement[at+1:], statement[:at])):
                count = _constant(value, constants)
                key = _length_key(term)
                if count is not None and count >= 0 and key.startswith('length '):
                    lengths[key] = count
    return lengths


@dataclass
class OwnedSeed:
    state: SymbolicState
    ownership: dict
    resources: list
    facts: list
    reports: list


def seed_owned_resources(seed, *, entry_pc, vocabulary, constants=None, facts=(), address_width=64):
    """Bind only source-owned resources. Keep unresolved lengths symbolic.

    constants maps source identifiers to exact integers and source origins.
    The caller supplies domain-specific separation facts through the generic IR.
    """
    constants = constants or {}
    provenance = {'public_seed_sha256': seed['_input_sha256'], 'source_bindings': seed['source_bindings']}
    ownership = ownership_from_assertion_tree(seed['assertion_tree'], provenance=provenance)
    lengths = _source_lengths(ownership, constants)
    state = SymbolicState(registers={'PC': bits(entry_pc, address_width)})
    resources, derived, reports = [], list(facts), []
    witnesses = {binder['name']: Expr.from_dict(binder['expression']) for binder in ownership['binders']
                 if 'expression' in binder}
    for component in ownership['components']:
        node = component['seed_component']
        if component['kind'] == 'register':
            witness = node.get('symbolic_witness')
            value = witnesses[witness] if witness else source_bv_expression(node['value_coq'], constants, node['width'])
            state.registers[component['name']] = value
            continue
        if component['kind'] not in ('byte_array', 'unknown_byte_array'):
            continue
        base = source_z_expression(component['address_z'], constants, address_width)
        array = Expr.from_dict(node['byte_array_expr']) if component['kind'] == 'byte_array' else None
        if array is not None and node.get('element_bits') != 8:
            raise ValueError('The public array has no source-established eight-bit element type')
        original_length = node['length_original_coq']
        length = lengths.get(_length_key(original_length))
        if length is None:
            length = _constant(original_length, constants)
        if length is None:
            length = input_expr(original_length, None)
            reports.append({'kind': 'symbolic_owned_length', 'resource_id': component['id'], 'term': original_length})
        fraction = component['fraction'][1:-1] if component['fraction'] is not None else 'DfracOwn 1'
        full = re.fullmatch(r'DfracOwn\s+(?:1(?:%Qp)?|\(1(?:%Qp)?\))', _strip_enclosure(fraction)) is not None
        resource = OwnedBytes(component['id'], base, component['address_z'], array, length,
                              True if full else None, fraction, component, provenance, 8)
        resources.append(resource)
        state.memory.append(MemoryRegion(base, byte_array=array, length=length,
                                         uninitialized=component['kind'] == 'unknown_byte_array', ownership_id=component['id']))
        rule_kind = 'owned_byte_array' if array is not None else 'uninitialized_stack_span'
        rules = [{'kind': row['kind'], 'source_bindings': [
                    {key: binding[key] for key in ('path', 'sha256', 'declaration')}
                    for binding in row.get('source_bindings', [])]}
                 for row in vocabulary['rows'] if row['kind'] in (rule_kind, 'permission_fraction')]
        origin = {'seed_component': component['id'], 'source_rules': rules, **provenance}
        if full:
            derived.append({'fact_id': component['id']+':permission', 'kind': 'permission',
                            'terms': {'resource_id': component['id'], 'fraction': fraction,
                                      'coq_statement': f'({fraction}) = DfracOwn 1'},
                            'origin': origin, 'status': 'derived-by-pass'})
        derived.append({'fact_id': component['id']+':nonwrap', 'kind': 'nonwrap',
                        'terms': {'resource_id': component['id'], 'original_address_z': component['address_z'],
                                  'original_length': original_length,
                                  'coq_statement': f'(0 <= ({component["address_z"]}) /\\ '
                                  f'Z.add ({component["address_z"]}) '
                                  f'({"Z.of_nat ("+original_length+")" if array is not None else original_length}) <= 2^64)%Z'},
                        'origin': origin, 'status': 'derived-by-pass'})
    state.reports.append({'kind': 'source_owned_seed', 'ownership_ids': [r.id for r in resources],
                          'uninitialized_values_created': False})
    return OwnedSeed(state, ownership, resources, derived, reports)
