"""Project explicit Level 1 layout clauses without extending an entry assertion.

The output is untrusted generator input. Each fact retains its exact source
clause and substitution. A later native proof must establish the full contract.
"""
import ast
from copy import deepcopy
import hashlib
from pathlib import Path
import re

from entry_seed import definition_body
from check_data_only_lemmas import rocq_commands
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


def numeric_constant_body(source, declaration):
    """Read numeric abbreviations without changing the entry-resource parser."""
    commands = rocq_commands(source)
    notations = [command for command in commands if len(command) > 3
                 and [token for token, _ in command[:3]] == ["Notation", declaration, ":="]]
    if not notations:
        return definition_body(source, declaration)
    definitions = [command for command in commands if any(
        token == "Definition" and index + 1 < len(command)
        and command[index + 1][0] == declaration
        for index, (token, _) in enumerate(command))]
    if len(notations) != 1 or definitions:
        raise ValueError('The numeric source declaration is ambiguous.')
    command = notations[0]
    if [token for token, _ in command[-4:]] != ['(', 'only', 'parsing', ')']:
        raise ValueError('A numeric notation must use only parsing.')
    body = _strip_enclosure(source[command[2][1] + 2:command[-4][1]].strip())
    casts = list(_top_positions(body, ':'))
    if casts:
        if len(casts) != 1 or _strip_enclosure(body[casts[0] + 1:]) not in {
                'Z', 'N', 'nat', 'positive', 'Coq.Numbers.BinNums.Z',
                'Coq.Numbers.BinNums.N', 'Coq.Numbers.BinNums.positive',
                'Coq.Init.Datatypes.nat'}:
            raise ValueError('The numeric notation has an unsupported type annotation.')
        body = body[:casts[0]].strip()
    closed_integer(body)
    return body


def constant_from_source(origin):
    source = read_source(origin)
    body = numeric_constant_body(source, origin['declaration'])
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
                          resource_roles, source_constants, interval_layout, layout_projections=None):
    """Project source clauses and a bounded stack interval from a checked layout.

    interval_layout names existing source terms. It supplies no numeric bound.
    Closed values come from separately hash-bound source constants.
    Optional projections name their parameters and literals in that same source.
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
    projections = layout_projections or {}
    if layout_projections is not None and (not isinstance(projections, dict)
            or not {'source'} < set(projections) <= {'source', 'output', 'return'}
            or projections['source'] != layout_source):
        raise ValueError('The optional layout projections lack their exact source binding.')

    def projected_clauses(statements, label):
        selected = []
        for statement in statements:
            matches = [clause for clause in clauses if _key(clause) == _key(statement)]
            if len(matches) != 1:
                raise ValueError('A required source ' + label + ' is absent or ambiguous.')
            selected.append(matches[0])
        return selected

    def descriptor(role, keys):
        value = projections[role]
        if not isinstance(value, dict) or set(value) != set(keys) or any(not isinstance(v, str) for v in value.values()):
            raise ValueError('An optional layout descriptor has unsupported fields.')
        if value['pointer'] not in arguments:
            raise ValueError('An optional layout pointer is not a source parameter.')
        return value

    projection_constants = {}

    def source_integer(term):
        if term not in source_constants:
            return closed_integer(term)
        bound = source_constants[term]
        if (not isinstance(bound, dict) or type(bound.get('value')) is not int or not bound.get('origin')
                or constant_from_source(bound['origin'])['value'] != bound['value']):
            raise ValueError('An optional layout constant differs from its source.')
        projection_constants[term] = deepcopy(bound)
        return bound['value']

    output = descriptor('output', {'pointer', 'extent'}) if 'output' in projections else None
    if output is not None:
        pointer, extent = output['pointer'], output['extent']
        length = source_integer(extent)
        if not 0 < length <= ram_end - ram_base:
            raise ValueError('The complete output array exceeds the source RAM interval.')
        selected = projected_clauses([f'0 <= {pointer}', f'{pointer} + {extent} < {modulus}',
                                     f'{base} <= {pointer}', f'{pointer} + {extent} <= {end}'], 'output/RAM bound')
        facts.append({'fact_id': 'layout:output-interval', 'kind': 'bounds', 'status': 'supplied',
                      'terms': {'unsigned_interval': {
                          'expression': source_z_expression(arguments[pointer], source_constants).to_dict(),
                          'minimum': ram_base, 'maximum': ram_end - length,
                          'ram_base': ram_base, 'ram_end': ram_end}},
                      'origin': {**origin, 'source_clauses': selected, 'descriptor': layout_projections,
                                 'constants': {**{term: source_constants[term] for term in values},
                                               **deepcopy(projection_constants)},
                                 'derivation': 'Conjunction projection, closed subtraction, and unsigned non-wrap.'}})
    pairs = [('input', 'output'), ('input', 'stack'), ('output', 'stack')]
    separate = [(i, clause) for i, clause in enumerate(clauses)
                if clause.startswith('separateRanges ')]
    if len(separate) != 3:
        raise ValueError('The source layout has no exact three-range separation.')
    # Validate each complete source application before assigning ownership IDs.
    # Preserve the original adapter when callers request no new projection.
    output_pointer, output_extent = (output['pointer'], output['extent']) if output else ('resultPointer', '40')
    expected_separation = [
        f'separateRanges inputPointer inputLength {output_pointer} {output_extent}',
        f'separateRanges inputPointer inputLength ({stack} - {frame}) {frame}',
        f'separateRanges {output_pointer} {output_extent} ({stack} - {frame}) {frame}']
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
    # Keep the modulus equation separate from its unsigned range. Both are
    # existing layout conjuncts, not new assumptions about a return path.
    if 'return' in projections:
        returned = descriptor('return', {'pointer', 'modulus', 'residue'})
        pointer, period, residue = (returned[key] for key in ('pointer', 'modulus', 'residue'))
        count, remainder = source_integer(period), source_integer(residue)
        if not 1 < count <= word or count & (count - 1) or not 0 <= remainder < count:
            raise ValueError('The source return congruence is unsupported.')
        selected = projected_clauses([f'0 <= {pointer} < {modulus}',
                                     f'{pointer} mod {period} = {residue}'], 'return alignment')
        facts.append({'fact_id': 'layout:return-alignment', 'kind': 'alignment', 'status': 'supplied',
                      'terms': {'alignment': {
                          'expression': source_z_expression(arguments[pointer], source_constants).to_dict(),
                          'modulus': count, 'residue': remainder}},
                      'origin': {**origin, 'source_clauses': selected, 'descriptor': layout_projections,
                                 'constants': deepcopy(projection_constants),
                                 'derivation': 'Conjunction projection and unsigned non-wrap.'}})
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
