"""Solve source join relations by exact coefficients, not path selection."""
from fractions import Fraction
from itertools import combinations

try:
    from .symbolic_state import Expr, bits, operation
except ImportError:
    from symbolic_state import Expr, bits, operation


def affine_form(value):
    """Use a modular affine form. Unsupported arithmetic remains an atom."""
    width = value.width
    if type(width) is not int or not 0 < width <= 128:
        raise ValueError('An affine value needs a closed bitvector width')
    def unbound(expression):
        return expression.op in {'unknown_input', 'unknown_read'} or any(unbound(arg) for arg in expression.args)
    if unbound(value):
        raise ValueError('An affine atom has no source binding')
    modulus = 1 << width

    def balanced(coefficient):
        coefficient %= modulus
        return coefficient - modulus if coefficient >= modulus // 2 else coefficient

    def add(left, right, factor=1):
        result = dict(left)
        for atom, coefficient in right.items():
            result[atom] = balanced(result.get(atom, 0) + factor * coefficient)
            if result[atom] == 0:
                del result[atom]
        return result

    if value.op == 'bits':
        return {} if value.value == 0 else {None: balanced(value.value)}
    if value.op in {'bvadd', 'bvsub'}:
        if any(argument.width != width for argument in value.args):
            raise ValueError('An affine operation changes width')
        return add(affine_form(value.args[0]), affine_form(value.args[1]), 1 if value.op == 'bvadd' else -1)
    if value.op == 'bvneg':
        return add({}, affine_form(value.args[0]), -1)
    if value.op == 'bvmul' and any(argument.op == 'bits' for argument in value.args):
        scalar, word = value.args if value.args[0].op == 'bits' else tuple(reversed(value.args))
        if scalar.width != width or word.width != width:
            raise ValueError('An affine multiplication changes width')
        return add({}, affine_form(word), scalar.value)
    return {value: 1}


def _solve(matrix, variables):
    rows = [[Fraction(coefficient) for coefficient in row] for row in matrix]
    pivots, position = [], 0
    for column in range(variables):
        pivot = next((index for index in range(position, len(rows)) if rows[index][column]), None)
        if pivot is None:
            continue
        rows[position], rows[pivot] = rows[pivot], rows[position]
        scale = rows[position][column]
        rows[position] = [coefficient / scale for coefficient in rows[position]]
        for index, row in enumerate(rows):
            if index != position and row[column]:
                scale = row[column]
                rows[index] = [left - scale * right for left, right in zip(row, rows[position])]
        pivots.append(column)
        position += 1
    if any(not any(row[:-1]) and row[-1] for row in rows):
        return None
    result = [Fraction(0) for _ in range(variables)]
    for index, column in enumerate(pivots):
        result[column] = rows[index][-1]
    return result if all(value.denominator == 1 for value in result) else None


def _scaled(value, coefficient):
    """Keep a modular coefficient compact instead of expanding repeated sums."""
    if abs(coefficient) == 1:
        return value
    return operation('bvmul', bits(abs(coefficient), value.width), value)


def affine_eliminate(targets, basis, *, expressions, register_names):
    """Prefer register-only solutions, then the fewest source terms.

    basis maps each name to one expression per edge. expressions supplies that
    name's expression in the generalized context. No Boolean selector enters
    the equation system. A rational-only or unsupported relation refuses.
    """
    if not targets or set(basis) != set(expressions) or set(register_names) - set(basis):
        raise ValueError('An affine join needs a complete ordered source basis')
    width = targets[0].width
    if any(value.width != width for value in targets):
        raise ValueError('Affine target widths differ')
    for name, values in basis.items():
        if len(values) != len(targets) or expressions[name].width != width or any(v.width != width for v in values):
            raise ValueError('An affine basis changes its width or edge count')
    forms = {name: [affine_form(value) for value in values] for name, values in basis.items()}
    wanted = [affine_form(value) for value in targets]
    names = list(basis)
    registers = [name for name in names if name in register_names]

    def candidates():
        for size in range(len(registers) + 1):
            yield from combinations(registers, size)
        for size in range(1, len(names) + 1):
            for group in combinations(names, size):
                if any(name not in register_names for name in group):
                    yield group

    for selected in candidates():
        matrix = []
        for index, target in enumerate(wanted):
            atoms = set(target) | {None}
            for name in selected:
                atoms.update(forms[name][index])
            for atom in sorted(atoms, key=repr):
                matrix.append([*(forms[name][index].get(atom, 0) for name in selected),
                               int(atom is None), target.get(atom, 0)])
        solution = _solve(matrix, len(selected) + 1)
        if solution is None:
            continue
        def balanced(value):
            residue = int(value) % (1 << width)
            return residue - (1 << width) if residue >= 1 << (width - 1) else residue
        coefficients = {name: balanced(value) for name, value in zip(selected, solution[:-1]) if balanced(value)}
        constant = balanced(solution[-1])
        value = bits(constant, width)
        for name, coefficient in coefficients.items():
            if coefficient > 0:
                value = operation('bvadd', value, _scaled(expressions[name], coefficient))
        for name, coefficient in coefficients.items():
            if coefficient < 0:
                value = operation('bvsub', value, _scaled(expressions[name], coefficient))
        # Recheck modular coefficients independently on every supplied edge.
        for index, target in enumerate(wanted):
            reconstructed = bits(constant, width)
            for name, coefficient in coefficients.items():
                reconstructed = operation('bvadd' if coefficient > 0 else 'bvsub', reconstructed,
                                          _scaled(basis[name][index], coefficient))
            if affine_form(reconstructed) != target:
                raise ValueError('An affine solution failed exact source substitution')
        return {'status': 'generated', 'expression': value.to_dict(), 'coq': value.coq(),
                'coefficients': coefficients, 'constant': constant, 'edge_count': len(targets),
                'certificate': 'exact_modular_source_coefficients', 'proof_established': False}
    return {'status': 'refused', 'kind': 'join_affine_refusal', 'edge_count': len(targets),
            'detail': 'No supported integral affine relation holds on every source edge', 'proof_established': False}
