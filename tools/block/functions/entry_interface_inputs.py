"""Bind a function's source-pass inputs from its Level-1 entry interface.

The function profile's `entry_interface` row names the source file, the entry
resources `<fn>EntryResources` and the well-formedness predicate
`<fn>ArgsWellFormed`. The public seed is the entry resources: its existential
register witnesses, its registers fixed to `Z_to_bv 64 (field args)` or to a
`bv` field, and its `↦ₘ∗` and `↦ₘ?` ownership. Its well-formedness conjunct
becomes the domain component.

The domain facts are conjuncts of the well-formedness predicate, each kept only
in a shape the forward pass consumes:
- an exact or a minimum constant length of an owned array;
- the alignment `Q mod M = 0` of a fixed register's quantity;
- a closed interval of a fixed register's quantity, from linear bounds with
  constant ends (the RAM ends come from the machine map);
- the separation of two owned ranges, through a definition whose body is
  `p + n <= q \\/ q + m <= p`.
Every other conjunct stays recorded and unused. Nothing is added beyond a
conjunct, and no proof runs. Traces and the CFG come from `--trace-root`.

Usage: entry_interface_inputs.py --function NAME --output DIR --vocabulary VOCABULARY.json
                                 [--trace-root DIR]
"""
from pathlib import Path
import argparse, json, re, shutil, sys

ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(ROOT / 'tools/block'))
sys.path.insert(0, str(ROOT / 'tools/block/functions'))
from entry_seed import definition_body
from forward_resources import (_strip_enclosure, _top_positions, load_resource_vocabulary,
                               ownership_from_assertion_tree, parse_source_ownership)
from function_profiles import load_profile
from source_domain import conjunctions, constant_from_source
from symbolic_state import input_expr
from function_inputs import BASE, bind, system_shapes, trace_index

WORD = 2 ** 64
NOTATION = re.compile(r'Notation\s+(\w+)\s*:=\s*\(\(\s*([0-9]+|0x[0-9a-fA-F]+)\s*\)\s*:\s*Z\)\s*\(only parsing\)\.')
SEPARATE_BODY = 'p+n<=q\\/q+m<=p'


def normal(term):
    """One spelling of a term: single spaces, no enclosing parentheses, no `%Z`."""
    term = re.sub(r'%Z\b', '', ' '.join(term.split()))
    return _strip_enclosure(term).strip()


def notations(source, text):
    """The closed Z notations of the source, with their values and provenance."""
    values = {}
    for name, literal in NOTATION.findall(text):
        values[name] = constant_from_source(bind(source, declaration=name))
        if values[name]['value'] != int(literal, 0):
            raise ValueError('A notation value differs from its source text: ' + name)
    return values


class Linear:
    """A linear integer term: atom -> coefficient, plus a constant. None if not linear."""

    @staticmethod
    def parse(term, constants):
        term = normal(term)
        positions = list(_top_positions(term, '+')) + list(_top_positions(term, '-'))
        if positions:
            pieces, signs, start, sign = [], [], 0, 1
            for position in sorted(positions):
                if term[position] == '-' and (position == 0 or term[position - 1] in '(^*'):
                    continue
                pieces.append((sign, term[start:position])), signs.append(term[position])
                sign, start = (1 if term[position] == '+' else -1), position + 1
            pieces.append((sign, term[start:]))
            total = ({}, 0)
            for sign, piece in pieces:
                part = Linear.parse(piece, constants)
                if part is None:
                    return None
                total = Linear.add(total, part, sign)
            return total
        if re.fullmatch(r'[0-9]+|0x[0-9a-fA-F]+', term):
            return ({}, int(term, 0))
        if re.fullmatch(r'2\s*\^\s*64', term):
            return ({}, WORD)
        if term in constants:
            return ({}, constants[term]['value'])
        match = re.fullmatch(r'([0-9]+)\s*\*\s*(.+)', term)
        if match:
            part = Linear.parse(match[2], constants)
            return None if part is None else Linear.add(({}, 0), part, int(match[1]))
        if re.search(r'[*/^]|\bmod\b', term) or re.search(r'(?<![<>=])[<>=]', term):
            return None
        return ({term: 1}, 0)

    @staticmethod
    def add(left, right, scale=1):
        atoms = dict(left[0])
        for atom, coefficient in right[0].items():
            atoms[atom] = atoms.get(atom, 0) + scale * coefficient
        return ({atom: c for atom, c in atoms.items() if c}, left[1] + scale * right[1])


def comparisons(clause):
    """A conjunct `a <= b`, `a < b`, or a chain `a <= b <= c` as (left, relation, right) pairs."""
    text = normal(clause)
    if '\\/' in text or '/\\' in text:
        return None
    parts = re.split(r'\s*(<=|<)\s*', text)
    if len(parts) < 3 or len(parts) % 2 == 0:
        return None
    return [(parts[i], parts[i + 1], parts[i + 2]) for i in range(0, len(parts) - 2, 2)]


def bounds(clauses, constants):
    """Lower and upper bounds of atoms, propagated through the linear conjuncts."""
    rows = []
    for index, clause in enumerate(clauses):
        for left, relation, right in comparisons(clause) or []:
            a, b = Linear.parse(left, constants), Linear.parse(right, constants)
            if a is None or b is None:
                continue
            row = Linear.add(a, b, -1)   # row <= 0, or row < 0
            rows.append((Linear.add(row, ({}, 1)) if relation == '<' else row, index))
    low, high = {}, {}
    for _ in range(3):
        for (atoms, constant), index in rows:
            for atom, coefficient in atoms.items():
                if abs(coefficient) != 1:
                    continue
                # coefficient * atom <= -constant - sum(others)
                rest, known = -constant, True
                for other, c in atoms.items():
                    if other == atom:
                        continue
                    # subtract c * other: needs the smallest value of c * other
                    entry = low.get(other) if c > 0 else high.get(other)
                    if entry is None:
                        known = False
                        break
                    rest -= c * entry[0]
                if not known:
                    continue
                if coefficient == 1:
                    if atom not in high or rest < high[atom][0]:
                        high[atom] = (rest, index)
                else:
                    if atom not in low or -rest > low[atom][0]:
                        low[atom] = (-rest, index)
    return ({atom: value[0] for atom, value in low.items()}, {atom: value[0] for atom, value in high.items()},
            {atom: value[1] for atom, value in low.items()}, {atom: value[1] for atom, value in high.items()})


def public_seed(profile, contract, text):
    interface = profile['entry_interface']
    body = definition_body(text, interface['entry_resources'])
    parsed = parse_source_ownership(body, provenance=bind(contract, declaration=interface['entry_resources']))
    binders = []
    for prefix in parsed['existential_prefixes']:
        for names, kind in re.findall(r'\(([^:()]+):\s*([^()]+)\)', prefix):
            if kind.strip() != 'bv 64':
                raise ValueError('An entry witness is not a 64-bit register value: ' + prefix)
            binders += [{'name': name, 'type': 'bv 64', 'expression': input_expr(name, 64).to_dict()}
                        for name in names.split()]
    names = {binder['name'] for binder in binders}
    wellformed = '⌜' + interface['well_formed'] + ' args⌝'
    components = []
    for row in parsed['components']:
        node = {'kind': row['kind'], 'id': row['id'], 'original_component': row['source']}
        if row['kind'] == 'register':
            value = row['value'][len('RVal_Bits '):].strip()
            node.update(register=row['name'], width=64, value_coq=value)
            if value in names:
                node['symbolic_witness'] = value
        elif row['kind'] == 'byte_array':
            node.update(address_z=row['address_z'], byte_array_expr=input_expr(row['value'], None).to_dict(),
                        element_bits=8, length_original_coq='List.length (' + row['value'] + ')')
        elif row['kind'] == 'unknown_byte_array':
            node.update(kind='uninitialized_memory', address_z=row['address_z'],
                        length_original_coq=row['length'])
        elif normal(row['source']) == normal(wellformed):
            # The model entry adds the return link; the domain component is both facts.
            node.update(coq='⌜domain args⌝', original_component=row['source'])
        else:
            node.update(coq=row['source'])
        components.append(node)
    if not any(node.get('coq') == '⌜domain args⌝' for node in components):
        raise ValueError('The entry resources do not state ' + wellformed)
    tree = {'kind': 'exists', 'binders': binders, 'components': components}
    ownership_from_assertion_tree(tree, provenance={'binding': 'Level1 source'})
    domain = profile['domain_component']
    return {'schema': 'h1-public-entry-seed.v1', 'function': profile['cfg_function'], 'entry_pc': None,
            'source_bindings': [bind(contract)],
            'parameters': [{'name': 'args', 'type': profile.args_type}, {'name': 'returnAddress', 'type': 'Z'},
                           {'name': 'domain', 'type': profile.args_type + ' -> Prop'}],
            'domain_binding': {'source': interface['source'], 'model': interface['entry_resources'],
                               'actual_domain': domain[1:-1] if domain.startswith('⌜') else domain,
                               'handling': 'The model entry is the return link and the entry resources; '
                                           'the domain component states both.'},
            'assertion_tree': tree, 'BODY': body,
            'original_components': [row['source'] for row in parsed['components']],
            'source_facts_added': 0}


def domain(profile, contract, text, seed, constants, ram):
    wellformed = profile['entry_interface']['well_formed']
    clauses = conjunctions(definition_body(text, wellformed))
    origin = {'source': bind(contract, declaration=wellformed)}

    def clause(index):
        return {**origin, 'conjunct_index': index, 'source_clause': clauses[index]}

    components = seed['assertion_tree']['components']
    fixed = {}
    for node in components:
        if node['kind'] == 'register' and 'symbolic_witness' not in node:
            match = re.fullmatch(r'Z_to_bv 64 (.+)', normal(node['value_coq']))
            if match:
                fixed[normal(match[1])] = node
    arrays = {normal(Expr_value(node)): node for node in components if node['kind'] == 'byte_array'}
    ranges = {}   # resource id -> (address, {length spellings})
    for node in components:
        if node['kind'] == 'byte_array':
            value = normal(Expr_value(node))
            ranges[node['id']] = (normal(node['address_z']), {normal('Z.of_nat (length (' + value + '))')})
        elif node['kind'] == 'uninitialized_memory':
            length = normal(node['length_original_coq'])
            spellings = {length}
            if length in constants:
                spellings.add(str(constants[length]['value']))
            ranges[node['id']] = (normal(node['address_z']), spellings)
    facts, used = [], set()
    # Array lengths; they also give each owned array its length spellings.
    for index, item in enumerate(clauses):
        text_ = normal(item)
        match = re.fullmatch(r'length \((.+)\) = ([0-9]+)%nat', text_)
        if match and normal(match[1]) in arrays:
            node, count = arrays[normal(match[1])], int(match[2])
            ranges[node['id']][1].update({str(count), *[name for name, row in constants.items()
                                                        if row['value'] == count]})
            facts.append({'fact_id': 'wellformed:length-%d' % index, 'kind': 'bounds', 'status': 'supplied',
                          'terms': {'resource_id': node['id'], 'index': 0, 'count': count, 'coq_statement': item},
                          'origin': clause(index)})
            used.add(index)
            continue
        match = re.fullmatch(r'([0-9]+) <= Z\.of_nat \(length \((.+)\)\)', text_)
        if match and normal(match[2]) in arrays:
            facts.append({'fact_id': 'wellformed:length-%d' % index, 'kind': 'bounds', 'status': 'supplied',
                          'terms': {'resource_id': arrays[normal(match[2])]['id'], 'index': 0,
                                    'count': int(match[1]), 'coq_statement': item},
                          'origin': clause(index)})
            used.add(index)
            continue
        match = re.fullmatch(r'Z\.of_nat \(length \((.+)\)\) = (.+)', text_)
        if match and normal(match[1]) in arrays:
            # A length link names the array's length by a quantity; the separations use it,
            # and a fixed register's quantity is a length view for the path conditions.
            node, quantity = arrays[normal(match[1])], normal(match[2])
            ranges[node['id']][1].add(quantity)
            if quantity in fixed:
                facts.append({'fact_id': 'wellformed:length-view-%d' % index, 'kind': 'bounds',
                              'status': 'supplied',
                              'terms': {'resource_id': node['id'], 'coq_statement': item, 'length_view':
                                        input_expr('(Z_to_bv 64%N (' + quantity + '))', 64).to_dict()},
                              'origin': clause(index)})
                used.add(index)
    # Alignments and intervals of fixed register quantities.
    low, high, low_from, high_from = bounds(clauses, constants)
    for index, item in enumerate(clauses):
        match = re.fullmatch(r'(.+) mod ([0-9]+) = 0', normal(item))
        if match and normal(match[1]) in fixed:
            facts.append({'fact_id': 'wellformed:alignment-%d' % index, 'kind': 'alignment', 'status': 'supplied',
                          'terms': {'alignment': {
                              'expression': input_expr('(Z_to_bv 64%N (' + normal(match[1]) + '))', 64).to_dict(),
                              'modulus': int(match[2]), 'residue': 0}},
                          'origin': clause(index)})
            used.add(index)
    for quantity in sorted(fixed, key=lambda q: int(fixed[q]['register'][1:])):
        if quantity not in low or quantity not in high:
            continue
        minimum, maximum = low[quantity], high[quantity]
        if not 0 <= minimum <= maximum < WORD or (minimum, maximum) == (0, WORD - 1):
            continue
        interval = {'expression': input_expr('(Z_to_bv 64%N (' + quantity + '))', 64).to_dict(),
                    'minimum': minimum, 'maximum': maximum}
        if ram[0] <= minimum and maximum <= ram[1]:
            interval.update(ram_base=ram[0], ram_end=ram[1])
        facts.append({'fact_id': 'wellformed:interval-' + fixed[quantity]['register'], 'kind': 'bounds',
                      'status': 'supplied', 'terms': {'unsigned_interval': interval},
                      'origin': {**clause(low_from[quantity]), 'upper_bound': clause(high_from[quantity]),
                                 'derivation': 'linear bounds of the conjuncts; closed notations resolved'}})
        used.update({low_from[quantity], high_from[quantity]})
    # Separations of two owned ranges.
    for index, item in enumerate(clauses):
        head, *arguments = split_application(normal(item))
        if len(arguments) != 4 or head not in separating(text):
            continue
        pairs = [(normal(arguments[0]), normal(arguments[1])), (normal(arguments[2]), normal(arguments[3]))]
        ids = []
        for address, length in pairs:
            matches = [key for key, (start, spellings) in ranges.items() if start == address and length in spellings]
            ids.append(matches[0] if len(matches) == 1 else None)
        if None in ids:
            continue
        facts.append({'fact_id': 'wellformed:separate-%d' % index, 'kind': 'disjoint_ranges',
                      'status': 'supplied', 'terms': {'left': ids[0], 'right': ids[1], 'coq_statement': item},
                      'origin': clause(index)})
        used.add(index)
    return {'projection': {'facts': facts, 'original_wellformed_clauses': clauses,
                           'unused_clauses': [i for i in range(len(clauses)) if i not in used],
                           'entry_assertion_changed': False, 'premises_added': []},
            'constants': constants}


def Expr_value(node):
    return node['byte_array_expr']['value']


def split_application(term):
    """`f a b c` as [f, a, b, c] at the top level."""
    positions = list(_top_positions(term, ' '))
    pieces, start = [], 0
    for position in positions:
        if position > start:
            pieces.append(term[start:position])
        start = position + 1
    pieces.append(term[start:])
    return [piece for piece in pieces if piece]


def separating(text):
    """Definitions of the source whose body states that two ranges do not overlap."""
    names = set()
    for name, parameters in re.findall(r'Definition\s+(\w+)\s+\(([^)]*)\)\s*:\s*Prop\s*:=', text):
        params = parameters.split(':')[0].split()
        if len(params) != 4:
            continue
        body = re.sub(r'\s+', '', definition_body(text, name))
        p, n, q, m = params
        if body == '{p}+{n}<={q}\\/{q}+{m}<={p}'.format(p=p, n=n, q=q, m=m):
            names.add(name)
    return names


def ram_ends(mapfile):
    origin = bind(mapfile, declaration='defaultMap')
    base = constant_from_source({**origin, 'field': 'mapRamBase'})['value']
    size = constant_from_source({**origin, 'field': 'mapRamSize'})['value']
    return base, base + size


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--function', required=True)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--vocabulary', type=Path, required=True)
    parser.add_argument('--trace-root', type=Path, default=BASE,
                        help='checkout that holds build/stock-zisk and the closure traces')
    options = parser.parse_args()
    profile = load_profile(options.function)
    if 'entry_interface' not in profile.data:
        raise ValueError('The profile has no entry_interface row: ' + options.function)
    output = options.output.resolve()
    output.mkdir(exist_ok=False)
    contract = ROOT / profile['entry_interface']['source']
    machine = ROOT / 'InstrSpecs/Machine.v'
    mapfile = ROOT / 'ZesuSsz/Contracts/Machine.v'
    text = contract.read_text()
    vocabulary = output / 'VOCABULARY.json'
    shutil.copyfile(options.vocabulary, vocabulary)
    load_resource_vocabulary(vocabulary, bind(vocabulary)['sha256'])
    namespace = profile.get('trace_namespace', 'ZesuSsz.Stock.' + profile['function'][:1].upper()
                            + profile['function'][1:])
    index, function = trace_index(output, profile['cfg_function'], namespace, root=options.trace_root)
    constants = notations(contract, text)
    seed = public_seed(profile, contract, text)
    facts = domain(profile, contract, text, seed, constants, ram_ends(mapfile))
    (output / 'DOMAIN.json').write_text(json.dumps(facts, indent=2) + '\n')
    (output / 'SYSTEM-SHAPES.json').write_text(json.dumps(system_shapes(machine, mapfile), indent=2) + '\n')
    seed['entry_pc'] = hex(function['entry'])
    seed['source_domain_binding'] = bind(output / 'DOMAIN.json')
    (output / 'SEED.json').write_text(json.dumps(seed, indent=2, ensure_ascii=False) + '\n')
    manifest = {'schema': 'fp301.seed-manifest.v1', 'function': profile['cfg_function'],
                'domain': bind(output / 'DOMAIN.json'), 'seed': bind(output / 'SEED.json'),
                'trace_index': bind(index), 'generator': bind(Path(__file__))}
    (output / 'SEED-MANIFEST.json').write_text(json.dumps(manifest, indent=2) + '\n')
    print(json.dumps({'seed_manifest': bind(output / 'SEED-MANIFEST.json'),
                      'instructions': len(function['rows']), 'blocks': len(function['blocks']),
                      'facts': [fact['fact_id'] for fact in facts['projection']['facts']],
                      'unused_clauses': facts['projection']['unused_clauses']}))


if __name__ == '__main__':
    main()
