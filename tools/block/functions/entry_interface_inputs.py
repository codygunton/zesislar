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
  constant ends (closed arithmetic of numerals and notations is evaluated; the
  RAM ends come from the machine map);
- the separation of two ranges, through a definition whose body is
  `p + n <= q \\/ q + m <= p`: of the two owned ranges it names, or of every
  owned range that lies inside each named range;
- a word link `W A K = Q` (or `Q = W A K`): W is a definition whose body is the
  little-endian 64-bit word `little_endian_to_bv 8 (take 8 (drop (Z.to_nat
  offset) bytes))` (or that body written inline), A an owned array, K a closed
  offset and Q any integer term: the eight bytes of A at K, while unwritten, are
  the register value `Z_to_bv 64 Q` (the forward pass reads them as Q; when Q is
  the address of another owned array, accesses through the loaded word resolve
  to that array).
Every other conjunct stays recorded and unused, and the tool prints each one
with the reason it gives no fact. Nothing is added beyond a
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
WORD_BODY = 'little_endian_to_bv 8 (take 8 (drop (Z.to_nat {offset}) {bytes}))'


def normal(term):
    """One spelling of a term: single spaces, no enclosing parentheses, no `%Z`."""
    term = re.sub(r'%Z\b', '', ' '.join(term.split()))
    return _strip_enclosure(term).strip()


def register_view(quantity):
    """The 64-bit register value whose unsigned reading is the integer `quantity`.

    `bv_unsigned V` reads back as V itself (F44: bounds on bv_unsigned of the binder);
    any other quantity is cast with Z_to_bv.
    """
    match = re.fullmatch(r'bv_unsigned (.+)', normal(quantity))
    return normal(match[1]) if match else '(Z_to_bv 64%N (' + normal(quantity) + '))'


def required_sources(source, text):
    """The source and the ZesuSsz modules it requires directly, as (path, text)."""
    files = [(source, text)]
    for module in re.findall(r'Require\s+(?:Import|Export)\s+ZesuSsz\.([\w.]+)\.', text):
        path = ROOT / 'ZesuSsz' / (module.replace('.', '/') + '.v')
        if path.exists():
            files.append((path, path.read_text()))
    return files


def notations(source, text):
    """The closed Z notations of the source and of the ZesuSsz modules it requires,
    with their values and provenance."""
    values = {}
    for path, body in required_sources(source, text):
        for name, literal in NOTATION.findall(body):
            value = constant_from_source(bind(path, declaration=name))
            if value['value'] != int(literal, 0):
                raise ValueError('A notation value differs from its source text: ' + name)
            if name in values and values[name]['value'] != value['value']:
                raise ValueError('Two required modules give a notation different values: ' + name)
            values.setdefault(name, value)
    return values


TOKEN = re.compile(r'\s*(0x[0-9a-fA-F]+|[0-9]+|[A-Za-z_][\w.\']*|\*\*|[-+*^()])')


def closed_value(term, constants):
    """The value of a closed integer term: numerals, closed notations, `+`, `-`, `*`, `^`
    (right-associative, exponent at least 0) and parentheses; None for anything else."""
    term = normal(term)
    tokens, position = [], 0
    while position < len(term):
        match = TOKEN.match(term, position)
        if match is None:
            return None
        tokens.append(match[1])
        position = match.end()
    index = 0

    def peek():
        return tokens[index] if index < len(tokens) else None

    def take():
        nonlocal index
        index += 1
        return tokens[index - 1]

    def atom():
        token = take() if peek() is not None else None
        if token == '(':
            value = total()
            if take() != ')':
                raise ValueError
            return value
        if token == '-':
            return -power()
        if token is not None and re.fullmatch(r'[0-9]+|0x[0-9a-fA-F]+', token):
            return int(token, 0)
        if token in constants:
            return constants[token]['value']
        raise ValueError

    def power():
        base = atom()
        if peek() == '^':
            take()
            exponent = power()
            if exponent < 0:
                raise ValueError
            return base ** exponent
        return base

    def product():
        value = power()
        while peek() == '*':
            take()
            value *= power()
        return value

    def total():
        value = product()
        while peek() in ('+', '-'):
            value = value + product() if take() == '+' else value - product()
        return value

    try:
        value = total()
    except (ValueError, IndexError):
        return None
    return value if index == len(tokens) else None


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
        if term in constants:
            return ({}, constants[term]['value'])
        value = closed_value(term, constants)
        if value is not None:
            return ({}, value)
        # A product with one non-closed factor: the closed factors scale it.
        stars = list(_top_positions(term, '*'))
        if stars:
            factors = [term[start + 1 if start >= 0 else 0:end] for start, end in zip([-1] + stars, stars + [len(term)])]
            values = [closed_value(factor, constants) for factor in factors]
            open_ = [factor for factor, value in zip(factors, values) if value is None]
            if len(open_) != 1:
                return None
            scale = 1
            for value in values:
                scale *= 1 if value is None else value
            part = Linear.parse(open_[0], constants)
            return None if part is None else Linear.add(({}, 0), part, scale)
        if re.search(r'[*/^]|\bmod\b', term) or re.search(r'(?<![<>=])[<>=]', term):
            return None
        return ({term: 1}, 0)

    @staticmethod
    def add(left, right, scale=1):
        atoms = dict(left[0])
        for atom, coefficient in right[0].items():
            atoms[atom] = atoms.get(atom, 0) + scale * coefficient
        return ({atom: c for atom, c in atoms.items() if c}, left[1] + scale * right[1])


def _top_split(text, connective):
    """The parts of `text` between its top-level occurrences of a two-character connective (`\\/`, `/\\`)."""
    cuts = [position for position in _top_positions(text, connective[0])
            if text[position + 1:position + 2] == connective[1]]
    starts = [0] + [position + 2 for position in cuts]
    ends = cuts + [len(text)]
    return [normal(text[start:end]) for start, end in zip(starts, ends)]


def comparisons(clause):
    """A conjunct `a <= b`, `a < b`, or a chain `a <= b <= c` as (left, relation, right) pairs."""
    text = normal(clause)
    if '\\/' in text or '/\\' in text:
        return None
    parts = re.split(r'\s*(<=|<)\s*', text)
    if len(parts) < 3 or len(parts) % 2 == 0:
        return None
    return [(parts[i], parts[i + 1], parts[i + 2]) for i in range(0, len(parts) - 2, 2)]


BV_RANGE = 'bv_unsigned range'


def bounds(clauses, constants):
    """Lower and upper bounds of atoms, propagated through the linear conjuncts.

    An atom `bv_unsigned V` starts in [0, 2^64 - 1] (its source index is BV_RANGE)."""
    rows = []
    for index, clause in enumerate(clauses):
        for left, relation, right in comparisons(clause) or []:
            a, b = Linear.parse(left, constants), Linear.parse(right, constants)
            if a is None or b is None:
                continue
            row = Linear.add(a, b, -1)   # row <= 0, or row < 0
            rows.append((Linear.add(row, ({}, 1)) if relation == '<' else row, index))
    unsigned = {atom for (atoms, _), _ in rows for atom in atoms if re.fullmatch(r'bv_unsigned \S.*', atom)}
    low, high = {atom: (0, BV_RANGE) for atom in unsigned}, {atom: (WORD - 1, BV_RANGE) for atom in unsigned}
    for _ in range(3):
        for (atoms, constant), index in rows:
            for atom, coefficient in atoms.items():
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
                # coefficient * atom <= rest: an integer atom is at most floor(rest / coefficient)
                # (coefficient > 0) or at least ceil(rest / coefficient) (coefficient < 0).
                if coefficient > 0:
                    bound = rest // coefficient
                    if atom not in high or bound < high[atom][0]:
                        high[atom] = (bound, index)
                else:
                    bound = -(rest // -coefficient)
                    if atom not in low or bound > low[atom][0]:
                        low[atom] = (bound, index)
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
            cell = word_cell(row['source'], record_widths(text), names)
            if cell is not None:
                node['word_cell'] = cell
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


def record_widths(text):
    """Field name -> N for every record field of type `bv N` in the source."""
    widths = {}
    for body in re.findall(r'Record\s+\w+\s*:\s*Type\s*:=\s*\w*\s*\{(.*?)\}', text, re.S):
        for fields, width in re.findall(r'([\w\s]+?)\s*:\s*bv\s+([0-9]+)\s*(?:;|$)', body):
            widths.update({name: int(width) for name in fields.split()})
    return widths


def word_cell(source, widths, binders):
    """A word cell `A ↦ₘ V` (full permission, one value): its address, its value and the value's
    width, when V is a `bv N` record field applied to `args` (N a multiple of 8) or a 64-bit
    entry witness; None otherwise."""
    match = re.fullmatch(r'(.+?)\s*↦ₘ\s+(.+)', normal(source))
    if not match or re.search(r'↦ₘ', match[2]):
        return None
    value = normal(match[2])
    field = re.fullmatch(r'(\w+) args', value)
    width = widths.get(field[1]) if field else (64 if value in binders else None)
    if width is None or width % 8:
        return None
    return {'address_z': normal(match[1]), 'value_coq': value, 'width': width,
            **({'symbolic_witness': value} if value in binders else {})}


def domain(profile, contract, text, seed, constants, ram, notes=None):
    """The domain facts; NOTES (a dict), when given, receives conjunct index -> why it is unused."""
    wellformed = profile['entry_interface']['well_formed']
    clauses = conjunctions(definition_body(text, wellformed))
    origin = {'source': bind(contract, declaration=wellformed)}

    def clause(index):
        if index == BV_RANGE:
            return {'derivation': 'bv_unsigned of a 64-bit value lies in [0, 2^64)'}
        return {**origin, 'conjunct_index': index, 'source_clause': clauses[index]}

    components = seed['assertion_tree']['components']
    # A fixed register's integer quantity: Q for `Z_to_bv 64 Q`, or `bv_unsigned V` for a bv value V.
    fixed = {}
    for node in components:
        if node['kind'] == 'register' and 'symbolic_witness' not in node:
            value = normal(node['value_coq'])
            match = re.fullmatch(r'Z_to_bv 64 (.+)', value)
            fixed[normal(match[1]) if match else normal('bv_unsigned (' + value + ')')] = node
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
        # The array is an application in parentheses, or a constant's bare name.
        match = re.fullmatch(r"length (?:\((.+)\)|([\w.']+)) = ([0-9]+)%nat", text_)
        array = match and normal(match[1] or match[2])
        if match and array in arrays:
            node, count = arrays[array], int(match[3])
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
                                        input_expr(register_view(quantity), 64).to_dict()},
                              'origin': clause(index)})
                used.add(index)
    low, high, low_from, high_from = bounds(clauses, constants)
    # Length relations: `scale * Q + offset <= L`, where L spells an owned array's length and Q
    # is a fixed register's quantity inside the 64-bit range, so its register value is Q.
    lengths = {spelling: key for key, (_, spellings) in ranges.items() for spelling in spellings
               if not re.fullmatch(r'[0-9]+', spelling) and spelling not in constants}
    for index, item in enumerate(clauses):
        for left, relation, right in comparisons(item) or []:
            a, b = Linear.parse(left, constants), Linear.parse(right, constants)
            if a is None or b is None:
                continue
            atoms, constant = Linear.add(a, b, -1)
            constant += relation == '<'
            arrays_ = [atom for atom, c in atoms.items() if c == -1 and atom in lengths]
            others = [(atom, c) for atom, c in atoms.items() if atom not in arrays_]
            if len(arrays_) != 1 or len(others) != 1 or others[0][1] <= 0 or others[0][0] not in fixed:
                continue
            quantity, scale = others[0]
            if not (low.get(quantity, -1) >= 0 and high.get(quantity, WORD) < WORD):
                continue
            facts.append({'fact_id': 'wellformed:length-relation-%d' % index, 'kind': 'bounds',
                          'status': 'supplied',
                          'terms': {'resource_id': lengths[arrays_[0]], 'coq_statement': item,
                                    'length_relation': {
                                        'view': input_expr(register_view(quantity), 64).to_dict(),
                                        'scale': scale, 'offset': constant}},
                          'origin': {**clause(index), 'range': clause(low_from[quantity]),
                                     'derivation': 'the quantity lies in [0, 2^64), so its register value is it'}})
            used.add(index)
    # End bounds `bv_unsigned P + L <= bv_unsigned E` with P an owned initialized array's address and L
    # one of its length spellings, or the right side of a conjunct `Z.of_nat (length V) = L` on its value:
    # the array ends at or below E (symbolic_state._placed_end_refutation).
    length_equations = {}
    for index, item in enumerate(clauses):
        match = re.fullmatch(r'Z\.of_nat \((?:List\.)?length \((.+)\)\) = (.+)', normal(item))
        if match:
            length_equations[(normal(match[1]), normal(match[2]))] = index
    for index, item in enumerate(clauses):
        pairs = comparisons(item) or []
        if len(pairs) != 1 or pairs[0][1] != '<=':
            continue
        left, _, right = pairs[0]
        plus = [position for position in _top_positions(left, '+')]
        bound = re.fullmatch(r'bv_unsigned (.+)', right)
        if len(plus) != 1 or bound is None:
            continue
        address, length = normal(left[:plus[0]]), normal(left[plus[0] + 1:])
        owners = [node for node in components if node['kind'] == 'byte_array' and ranges[node['id']][0] == address
                  and (length in ranges[node['id']][1]
                       or (normal(Expr_value(node)), length) in length_equations)]
        base = re.fullmatch(r'bv_unsigned (.+)', address)
        if len(owners) != 1 or base is None:
            continue
        equation = length_equations.get((normal(Expr_value(owners[0])), length))
        facts.append({'fact_id': 'wellformed:end-bound-%d' % index, 'kind': 'bounds', 'status': 'supplied',
                      'terms': {'resource_id': owners[0]['id'], 'coq_statement': item, 'end_bound': {
                          'base': input_expr(normal(base[1]), 64).to_dict(),
                          'bound': input_expr(normal(bound[1]), 64).to_dict()}},
                      'origin': {**clause(index), **({'length': clause(equation)} if equation is not None else {}),
                                 'derivation': 'the owned array at the address with that length ends at or '
                                               'below the bound'}})
        used.add(index)
    # Low bounds `L <= bv_unsigned P` with P an owned initialized array's address and L closed: a conjunct,
    # or a disjunction each of whose alternatives has such a conjunct (L the least of them); the array
    # starts at or above L (symbolic_state._placed_low_refutation).
    addresses_ = {ranges[node['id']][0]: node for node in components if node['kind'] == 'byte_array'}
    for index, item in enumerate(clauses):
        least = None
        for alternative in _top_split(normal(item), '\\/'):
            found = {}
            for part in _top_split(_strip_enclosure(alternative), '/\\'):
                for left, relation, right in comparisons(part) or []:
                    value, address = closed_value(left, constants), normal(right)
                    if value is not None and address in addresses_:
                        found[address] = max(found.get(address, value), value + (relation == '<'))
            if least is None:
                least = found
            else:
                least = {address: min(value, found[address]) for address, value in least.items() if address in found}
        for address, value in sorted((least or {}).items()):
            base = re.fullmatch(r'bv_unsigned (.+)', address)
            if base is None or value <= 0:
                continue
            facts.append({'fact_id': 'wellformed:low-bound-%d' % index, 'kind': 'bounds', 'status': 'supplied',
                          'terms': {'resource_id': addresses_[address]['id'], 'coq_statement': item, 'low_bound': {
                              'base': input_expr(normal(base[1]), 64).to_dict(), 'minimum': value}},
                          'origin': {**clause(index), 'derivation': 'every alternative of the clause bounds the '
                                                                    'owned array address from below; the least'}})
            used.add(index)
    # Alignments and intervals of fixed register quantities (and, below, of word-link quantities).
    for index, item in enumerate(clauses):
        match = re.fullmatch(r'(.+) mod ([0-9]+) = 0', normal(item))
        if match and normal(match[1]) in fixed:
            facts.append({'fact_id': 'wellformed:alignment-%d' % index, 'kind': 'alignment', 'status': 'supplied',
                          'terms': {'alignment': {
                              'expression': input_expr(register_view(match[1]), 64).to_dict(),
                              'modulus': int(match[2]), 'residue': 0}},
                          'origin': clause(index)})
            used.add(index)
    for quantity in sorted(fixed, key=lambda q: int(fixed[q]['register'][1:])):
        if quantity not in low or quantity not in high:
            continue
        minimum, maximum = low[quantity], high[quantity]
        if not 0 <= minimum <= maximum < WORD or (minimum, maximum) == (0, WORD - 1):
            continue
        interval = {'expression': input_expr(register_view(quantity), 64).to_dict(),
                    'minimum': minimum, 'maximum': maximum}
        if ram[0] <= minimum and maximum <= ram[1]:
            interval.update(ram_base=ram[0], ram_end=ram[1])
        facts.append({'fact_id': 'wellformed:interval-' + fixed[quantity]['register'], 'kind': 'bounds',
                      'status': 'supplied', 'terms': {'unsigned_interval': interval},
                      'origin': {**clause(low_from[quantity]), 'upper_bound': clause(high_from[quantity]),
                                 'derivation': 'linear bounds of the conjuncts; closed notations resolved'}})
        used.update(index for index in (low_from[quantity], high_from[quantity]) if index != BV_RANGE)
    # Separations of two ranges: an owned range on each side, or every owned range that lies
    # inside each side's range (a range at a constant offset from the side's address with a
    # closed length that ends within the side's closed length): both are separate when the
    # sides are.
    separators = separating(contract, text)
    reasons = {}

    def contained(address, length):
        extent = Linear.parse(length, constants)
        start = Linear.parse(address, constants)
        if extent is None or extent[0] or start is None:
            return []
        inside = []
        for key, (owned, spellings) in ranges.items():
            offset = Linear.parse(owned, constants)
            sizes = [Linear.parse(spelling, constants) for spelling in spellings]
            sizes = [size[1] for size in sizes if size is not None and not size[0]]
            if offset is None or not sizes:
                continue
            delta = Linear.add(offset, start, -1)
            if not delta[0] and 0 <= delta[1] and delta[1] + max(sizes) <= extent[1]:
                inside.append(key)
        return inside

    for index, item in enumerate(clauses):
        head, *arguments = split_application(normal(item))
        if len(arguments) != 4 or head not in separators:
            continue
        pairs = [(normal(arguments[0]), normal(arguments[1])), (normal(arguments[2]), normal(arguments[3]))]
        ids = []
        for address, length in pairs:
            matches = [key for key, (start, spellings) in ranges.items() if start == address and length in spellings]
            ids.append(matches[0] if len(matches) == 1 else None)
        if None not in ids:
            facts.append({'fact_id': 'wellformed:separate-%d' % index, 'kind': 'disjoint_ranges',
                          'status': 'supplied', 'terms': {'left': ids[0], 'right': ids[1], 'coq_statement': item},
                          'origin': clause(index)})
            used.add(index)
            continue
        sides = [[key] if key is not None else contained(*pair) for key, pair in zip(ids, pairs)]
        if not all(sides):
            empty = [pair for pair, side in zip(pairs, sides) if not side]
            reasons[index] = ('separation: no owned range is the range or lies inside the range %s (an owned '
                              'range must start at a constant offset from its address and have a closed length '
                              'within its closed length)' % ' nor '.join('[%s, +%s)' % pair for pair in empty))
            continue
        for left in sides[0]:
            for right in sides[1]:
                facts.append({'fact_id': 'wellformed:separate-%d-%s-%s' % (index, left, right),
                              'kind': 'disjoint_ranges', 'status': 'supplied',
                              'terms': {'left': left, 'right': right, 'coq_statement': item},
                              'origin': {**clause(index), 'derivation': 'each owned range lies inside one side '
                                         'of the separated ranges'}})
        used.add(index)
    # Word links: the word of an owned array at a closed offset equals a quantity.
    readers = word_readers(contract, text)
    addresses = {normal(node['address_z']): node['id'] for node in components if node['kind'] == 'byte_array'}
    linked = set()

    def loaded_bounds(quantity, suffix, link):
        """Q's alignment and interval conjuncts as facts on the loaded register value `Z_to_bv 64 Q`
        (or V for Q = `bv_unsigned V`), as a fixed register's quantity gets them."""
        if quantity in fixed or quantity in linked:
            return
        linked.add(quantity)
        view = input_expr(register_view(quantity), 64).to_dict()
        for other, conjunct in enumerate(clauses):
            match = re.fullmatch(r'(.+) mod ([0-9]+) = 0', normal(conjunct))
            if match and normal(match[1]) == quantity and other not in used:
                facts.append({'fact_id': 'wellformed:alignment-%d' % other, 'kind': 'alignment',
                              'status': 'supplied', 'terms': {'alignment': {
                                  'expression': view, 'modulus': int(match[2]), 'residue': 0}},
                              'origin': {**clause(other), 'link': link}})
                used.add(other)
        minimum, maximum = low.get(quantity), high.get(quantity)
        if minimum is None or maximum is None or not 0 <= minimum <= maximum < WORD or (minimum, maximum) == (0, WORD - 1):
            return
        interval = {'expression': view, 'minimum': minimum, 'maximum': maximum}
        if ram[0] <= minimum and maximum <= ram[1]:
            interval.update(ram_base=ram[0], ram_end=ram[1])
        facts.append({'fact_id': 'wellformed:interval-' + suffix, 'kind': 'bounds', 'status': 'supplied',
                      'terms': {'unsigned_interval': interval},
                      'origin': {**clause(low_from[quantity]), 'upper_bound': clause(high_from[quantity]),
                                 'link': link, 'derivation': 'linear bounds of the conjuncts; the loaded '
                                                             'register value has this quantity'}})
        used.update(i for i in (low_from[quantity], high_from[quantity]) if i != BV_RANGE)

    for index, item in enumerate(clauses):
        if index in used:
            continue
        text_ = normal(item)
        sides = equation_sides(text_)
        parsed = None
        for word, quantity in ((sides, sides[::-1]) if sides else ()):
            parsed = word_term(word, readers)
            if parsed:
                break
        if parsed is None:
            mentions = any(re.search(r'(?<![\w.\'])%s(?![\w.\'])' % re.escape(name), text_) for name in readers)
            if mentions or 'little_endian_to_bv' in text_:
                reasons[index] = ('word link: the conjunct reads a word but is not `W A K = Q` with W the '
                                  'little-endian 64-bit word reader (only an unconditional equation is followed)')
            elif '->' in text_ and any(address in text_.split('->')[-1] for address in addresses):
                reasons[index] = ('word link: a conditional equation with an owned array address (a pointer that '
                                  'is null or that address) is not followed; only `W A K = Q` is')
            continue
        array, offset_term = parsed
        offset = closed_value(offset_term, constants)
        if array not in arrays:
            reasons[index] = 'word link: `%s` is not an owned array of the entry resources' % array
            continue
        if offset is None or offset < 0:
            reasons[index] = 'word link: the offset `%s` is not a closed non-negative integer' % offset_term
            continue
        terms = {'resource_id': arrays[array]['id'], 'offset': offset, 'size': 8,
                 'quantity': normal(quantity), 'coq_statement': item}
        if normal(quantity) in addresses:
            terms['target_resource_id'] = addresses[normal(quantity)]
        facts.append({'fact_id': 'wellformed:word-link-%d' % index, 'kind': 'word_link', 'status': 'supplied',
                      'terms': terms, 'origin': {**clause(index), 'derivation': (
                          'the eight bytes of the array at the offset, unwritten, are the little-endian word, '
                          'equal to the quantity, which lies in [0, 2^64): the loaded register value is '
                          'Z_to_bv 64 of the quantity')}})
        used.add(index)
        loaded_bounds(normal(quantity), 'link-%d' % index, clause(index))
    # A word cell's value is loaded as is: its `bv_unsigned` interval and alignment bound it too.
    for node in components:
        if 'word_cell' in node and 'symbolic_witness' not in node['word_cell']:
            loaded_bounds(normal('bv_unsigned (' + node['word_cell']['value_coq'] + ')'), 'cell-' + node['id'],
                          {'word_cell': node['id'], 'source_component': node['original_component']})
    unused = [i for i in range(len(clauses)) if i not in used]
    if notes is not None:
        for index in unused:
            notes[index] = reasons.get(index) or unused_reason(clauses[index], constants)
    return {'projection': {'facts': facts, 'original_wellformed_clauses': clauses,
                           'unused_clauses': unused,
                           'entry_assertion_changed': False, 'premises_added': []},
            'constants': constants}


def equation_sides(term):
    """The two sides of a conjunct `L = R` with one top-level `=` (not `<=`, `>=`, `<>`, `=>`), or None."""
    positions = [position for position in _top_positions(term, '=')
                 if term[position - 1:position] not in ('<', '>', '!', '=') and term[position + 1:position + 2] != '>']
    if len(positions) != 1 or any(term.find(token) >= 0 for token in ('->', '/\\', '\\/', '<->')):
        return None
    return normal(term[:positions[0]]), normal(term[positions[0] + 1:])


def word_term(term, readers):
    """(array, offset term) of the little-endian 64-bit word of an array at an offset, or None:
    `W A K` for a reader W (`word_readers`), or the reader's body written inline."""
    head, *arguments = split_application(normal(term))
    if head in readers and len(arguments) == 2:
        return normal(arguments[0]), normal(arguments[1])
    match = re.fullmatch(r'little_endian_to_bv 8 \(take 8 \((drop .+)\)\)', normal(term))
    pieces = split_application(match[1]) if match else []
    if len(pieces) != 3:
        return None
    cast = re.fullmatch(r'Z\.to_nat (.+)', normal(pieces[1]))
    return (normal(pieces[2]), normal(cast[1])) if cast else None


def word_readers(source, text):
    """Definitions of the source and its required modules `W (bytes : list byte) (offset : Z) : Z`
    whose body is the little-endian 64-bit word of `bytes` at `offset` (`WORD_BODY`)."""
    names = set()
    for _, body_text in required_sources(source, text):
        for name, parameters in re.findall(r'Definition\s+(\w+)\s*((?:\([^()]*\)\s*)+):\s*Z\s*:=', body_text):
            binders = [(binder, kind.strip()) for group, kind in re.findall(r'\(([^:()]+):([^()]+)\)', parameters)
                       for binder in group.split()]
            if [kind for _, kind in binders] != ['list byte', 'Z']:
                continue
            (array, _), (offset, _) = binders
            if normal(definition_body(body_text, name)) == WORD_BODY.format(offset=offset, bytes=array):
                names.add(name)
    return names


def unused_reason(item, constants):
    """Why a well-formedness conjunct gives no domain fact, for the tool's report."""
    pairs = comparisons(item)
    if pairs:
        for left, _, right in pairs:
            for term in (left, right):
                if Linear.parse(term, constants) is None:
                    return 'bound: the linear reader does not read the term `%s`' % normal(term)
        return ('bound: linear, but it bounds no fixed register quantity by constants and relates no owned '
                'array length to one fixed register quantity')
    return ('no consumed shape (length of an owned array, alignment or interval of a fixed register quantity, '
            'length relation, separation of owned ranges)')


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


def separating(source, text):
    """Definitions of the source and its required modules whose body states that
    two ranges do not overlap."""
    names = set()
    for _, body_text in required_sources(source, text):
        for name, parameters in re.findall(r'Definition\s+(\w+)\s+\(([^)]*)\)\s*:\s*Prop\s*:=', body_text):
            params = parameters.split(':')[0].split()
            if len(params) != 4:
                continue
            body = re.sub(r'\s+', '', definition_body(body_text, name))
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
    notes = {}
    facts = domain(profile, contract, text, seed, constants, ram_ends(mapfile), notes)
    (output / 'DOMAIN.json').write_text(json.dumps(facts, indent=2) + '\n')
    shapes = system_shapes(machine, mapfile)
    # A system register that the entry fixes to a quantity (as decodeItemSysRegs fixes
    # zisk_input_end): the interface row names the quantity.
    for name, quantity in profile['entry_interface'].get('exact_system_registers', {}).items():
        row, = [row for row in shapes['rows'] if row['key'] == name]
        row.update(shape='exact', value=input_expr(register_view(quantity), 64).to_dict())
        row.pop('symbol', None)
    (output / 'SYSTEM-SHAPES.json').write_text(json.dumps(shapes, indent=2) + '\n')
    seed['entry_pc'] = hex(function['entry'])
    seed['source_domain_binding'] = bind(output / 'DOMAIN.json')
    (output / 'SEED.json').write_text(json.dumps(seed, indent=2, ensure_ascii=False) + '\n')
    manifest = {'schema': 'fp301.seed-manifest.v1', 'function': profile['cfg_function'],
                'domain': bind(output / 'DOMAIN.json'), 'seed': bind(output / 'SEED.json'),
                'trace_index': bind(index), 'generator': bind(Path(__file__))}
    (output / 'SEED-MANIFEST.json').write_text(json.dumps(manifest, indent=2) + '\n')
    clauses = facts['projection']['original_wellformed_clauses']
    unused = [{'index': index, 'clause': normal(clauses[index]), 'reason': notes[index]}
              for index in facts['projection']['unused_clauses']]
    for row in unused:
        print('entry_interface_inputs: %s conjunct %d unused (%s): %s'
              % (profile['entry_interface']['well_formed'], row['index'], row['reason'], row['clause']),
              file=sys.stderr)
    print(json.dumps({'seed_manifest': bind(output / 'SEED-MANIFEST.json'),
                      'instructions': len(function['rows']), 'blocks': len(function['blocks']),
                      'facts': [fact['fact_id'] for fact in facts['projection']['facts']],
                      'unused_clauses': facts['projection']['unused_clauses'], 'unused': unused}))


if __name__ == '__main__':
    main()
