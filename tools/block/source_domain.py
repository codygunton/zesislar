"""Project explicit Level 1 layout clauses without extending an entry assertion.

The output is untrusted generator input. Each fact retains its exact source
clause and substitution. A later native proof must establish the full contract.
"""
import ast
import hashlib
from pathlib import Path
import re

from entry_seed import definition_body
from forward_resources import _strip_enclosure, _top_positions
from resource_seed import source_z_expression
from render_support import declared_binders


def read_source(binding):
    data = Path(binding['path']).read_bytes()
    if hashlib.sha256(data).hexdigest() != binding['sha256']:
        raise ValueError('The domain source hash differs.')
    return data.decode()


def conjunctions(body):
    body = _strip_enclosure(body)
    positions = [-2, *[p for p in _top_positions(body, '/') if body[p:p+2] == '/\\'], len(body)]
    return [body[left+2:right].strip() for left, right in zip(positions, positions[1:])]


def substitute(source, arguments):
    # One substitution pass prevents replacement text from becoming another key.
    pattern = r'\b(' + '|'.join(re.escape(name) for name in arguments) + r')\b'
    return re.sub(pattern, lambda match: '(' + arguments[match[0]] + ')', source)


def _key(source):
    return re.sub(r'[\s()]', '', source)


def closed_integer(source):
    """Evaluate only bounded literal integer arithmetic, never source code."""
    source = re.sub(r'%(?:Z|N|nat)\b', '', source).replace('^', '**').strip()
    def visit(node):
        if isinstance(node, ast.Constant) and type(node.value) is int:
            result = node.value
        elif isinstance(node, ast.UnaryOp) and isinstance(node.op, ast.USub):
            result = -visit(node.operand)
        elif isinstance(node, ast.BinOp) and isinstance(node.op, (ast.Add, ast.Sub, ast.Mult, ast.Pow)):
            left, right = visit(node.left), visit(node.right)
            if isinstance(node.op, ast.Pow):
                if not 0 <= right <= 128:
                    raise ValueError('The source exponent is unsupported.')
                result = left ** right
            elif isinstance(node.op, ast.Add):
                result = left + right
            elif isinstance(node.op, ast.Sub):
                result = left - right
            else:
                result = left * right
        else:
            raise ValueError('The source integer contains a symbolic or unsupported term.')
        if abs(result) > 2**256:
            raise ValueError('The source integer exceeds the supported size.')
        return result
    try:
        return visit(ast.parse(source, mode='eval').body)
    except SyntaxError as error:
        raise ValueError('The source integer syntax is unsupported.') from error


def constant_from_source(origin):
    source = read_source(origin)
    body = definition_body(source, origin['declaration'])
    if 'field' in origin:
        values = re.findall(r'\b' + re.escape(origin['field']) + r'\s*:=\s*([^;|]+)', body)
        if len(values) != 1:
            raise ValueError('The source record field is absent or ambiguous.')
        value = closed_integer(values[0])
    elif 'sum_fields' in origin:
        fields = origin['sum_fields']
        if len(fields) != 2 or _key(body.removesuffix('%Z')) != _key(
                f'({fields[0]} {origin["parameter"]} + {fields[1]} {origin["parameter"]})'):
            raise ValueError('The source endpoint is not the declared field sum.')
        record = origin['record_source']
        value = sum(constant_from_source({**record, 'field': name})['value'] for name in fields)
    else:
        value = closed_integer(body)
    return {'value': value, 'type': 'Z', 'origin': dict(origin)}


def project_layout_domain(*, layout_source, wellformed_source, arguments,
                          resource_roles, source_constants, interval_layout):
    """Project source clauses and a bounded stack interval from a checked layout.

    interval_layout names existing source terms. It supplies no numeric bound.
    Closed values come from separately hash-bound source constants.
    """
    layout_text = read_source(layout_source)
    layout = definition_body(layout_text, layout_source['declaration'])
    wellformed = definition_body(read_source(wellformed_source), wellformed_source['declaration'])
    clauses = conjunctions(layout)
    wf_clauses = conjunctions(wellformed)
    parameters = declared_binders(layout_text, layout_source['declaration'])
    if set(arguments) != {parameter['name'] for parameter in parameters}:
        raise ValueError('The layout substitution omits or adds a parameter.')
    application = layout_source['declaration'] + ' ' + ' '.join(
        '(' + arguments[parameter['name']] + ')' for parameter in parameters)
    if sum(_key(clause) == _key(application) for clause in wf_clauses) != 1:
        raise ValueError('The wellformed domain does not contain this exact layout application.')
    if set(resource_roles) != {'input', 'output', 'stack'} or len(set(resource_roles.values())) != 3:
        raise ValueError('The domain needs three distinct existing ownership IDs.')
    required = {'stack', 'frame_size', 'modulus', 'ram_base', 'ram_end'}
    if set(interval_layout) != required:
        raise ValueError('The interval layout has missing or unsupported fields.')
    stack, frame, modulus, base, end = (interval_layout[k] for k in
                                       ('stack', 'frame_size', 'modulus', 'ram_base', 'ram_end'))
    expected = [f'{frame} <= {stack} < {modulus}',
                f'{base} + {frame} <= {stack}', f'{stack} <= {end}']
    indices = []
    for statement in expected:
        matches = [i for i, clause in enumerate(clauses) if _key(clause) == _key(statement)]
        if len(matches) != 1:
            raise ValueError('A required source stack/RAM bound is absent or ambiguous.')
        indices.append(matches[0])
    values = {}
    for term in (frame, modulus, base, end):
        value = source_constants.get(term)
        if not isinstance(value, dict) or type(value.get('value')) is not int or not value.get('origin'):
            raise ValueError('A layout constant lacks its source value or provenance.')
        if constant_from_source(value['origin'])['value'] != value['value']:
            raise ValueError('The supplied layout constant differs from its source.')
        values[term] = value['value']
    size, word, ram_base, ram_end = (values[t] for t in (frame, modulus, base, end))
    if word != 2**64 or not 0 < size or not 0 <= ram_base < ram_base + size <= ram_end < word:
        raise ValueError('The source RAM interval is unsupported.')
    origin = {'sources': [dict(layout_source), dict(wellformed_source)],
              'layout_declaration': layout_source['declaration'],
              'wellformed_declaration': wellformed_source['declaration'],
              'parameter_substitution': dict(arguments)}
    facts = []
    pairs = [('input', 'output'), ('input', 'stack'), ('output', 'stack')]
    separate = [(i, clause) for i, clause in enumerate(clauses)
                if clause.startswith('separateRanges ')]
    if len(separate) != 3:
        raise ValueError('The source layout has no exact three-range separation.')
    # Validate each complete source application before assigning ownership IDs.
    expected_separation = [
        'separateRanges inputPointer inputLength resultPointer 40',
        f'separateRanges inputPointer inputLength ({stack} - {frame}) {frame}',
        f'separateRanges resultPointer 40 ({stack} - {frame}) {frame}']
    for (index, clause), (left, right), expected_clause in zip(separate, pairs, expected_separation):
        if _key(clause) != _key(expected_clause):
            raise ValueError('A source separation application differs from its ownership roles.')
        facts.append({'fact_id': f'layout:{index}', 'kind': 'disjoint_ranges', 'status': 'supplied',
                      'terms': {'left': resource_roles[left], 'right': resource_roles[right],
                                'coq_statement': substitute(clause, arguments)},
                      'origin': {**origin, 'conjunct_index': index, 'source_clause': clause}})
    for index, clause in enumerate(wf_clauses):
        if index == 0:
            # Require the source equality, rather than infer an array length.
            if _key(clause) != _key('decodeItemInputLength args = Z.of_nat (List.length (decodeItemInputBytes args))'):
                raise ValueError('The input-length source equality is unsupported.')
            terms = {'resource_id': resource_roles['input'],
                     'length_view': source_z_expression('decodeItemInputLength args', source_constants).to_dict(),
                     'coq_statement': clause}
            facts.append({'fact_id': 'wellformed:input-length', 'kind': 'bounds',
                          'status': 'supplied', 'terms': terms,
                          'origin': {**origin, 'source_clause': clause, 'conjunct_index': index}})
    expression = source_z_expression(arguments[stack], source_constants)
    facts.append({'fact_id': 'layout:stack-interval', 'kind': 'bounds', 'status': 'supplied',
                  'terms': {'unsigned_interval': {'expression': expression.to_dict(),
                            'minimum': ram_base + size, 'maximum': ram_end,
                            'ram_base': ram_base, 'ram_end': ram_end}},
                  'origin': {**origin, 'source_clauses': [clauses[i] for i in indices],
                             'constants': {term: source_constants[term] for term in values},
                             'derivation': 'Conjunction projection, closed addition, and unsigned non-wrap.'}})
    return {'facts': facts, 'original_layout_clauses': clauses,
            'original_wellformed_clauses': wf_clauses, 'source_bindings': origin['sources'],
            'entry_assertion_changed': False, 'premises_added': []}
