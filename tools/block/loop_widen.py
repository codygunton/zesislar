"""Propose loop-head seeds from source traces, without proving entailments.

Every syntactic register write becomes a binder. Algebraic checks are separate
from unsigned non-wrap and byte-window obligations. An unavailable check drops
its relation and records the reason; it never supplies a guessed image.
"""
from dataclasses import dataclass, field
import re

try:
    from .guard_normal_form import GuardNormalForm
    from .resource_seed import source_z_expression
    from .forward_resources import _strip_enclosure, _top_positions
    from .forward_design import _footprint
    from .symbolic_state import Expr, bits, evaluate_block, input_expr, operation, parse_trace, _offset
except ImportError:
    from guard_normal_form import GuardNormalForm
    from resource_seed import source_z_expression
    from forward_resources import _strip_enclosure, _top_positions
    from forward_design import _footprint
    from symbolic_state import Expr, bits, evaluate_block, input_expr, operation, parse_trace, _offset


_REGISTER = re.compile(r'x(?:[0-9]|[12][0-9]|3[01])\Z')
_IDENTIFIER = re.compile(r"[A-Za-z_][A-Za-z_0-9']*\Z")


def _register_order(name):
    return int(name[1:])


def write_set(traces, universe):
    """Include conditional writes, even when a fault path skips them.

    _footprint supplies straight-path writes. Its branch intersection is right
    for liveness but insufficient for loop binders, so visit each branch too.
    """
    written = set()

    def visit(events):
        _, guaranteed = _footprint(events, set(universe))
        written.update(guaranteed)
        for event in events:
            if not isinstance(event, list) or not event:
                raise ValueError('A loop footprint needs parsed source events')
            if event[0] == 'write-reg' and len(event) > 1:
                name = event[1].strip('|')
                if _REGISTER.fullmatch(name):
                    written.add(name)
            if event[0] == 'cases':
                for branch in event[2:]:
                    if not isinstance(branch, list) or branch[:1] != ['trace']:
                        raise ValueError('A loop branch has no source trace')
                    visit(branch[1:])

    for source in traces:
        visit(parse_trace(source)[1:])
    return tuple(sorted((key for key in written if _REGISTER.fullmatch(key)),
                        key=_register_order))


def _linear(expression):
    """Return exact affine coefficients in the expression's bitvector ring."""
    width = expression.width
    if not isinstance(width, int) or width <= 0:
        raise ValueError('An affine expression needs a positive bitvector width')
    modulus = 1 << width
    if expression.op == 'bits':
        return expression.value, {}
    if expression.op in {'bvadd', 'bvsub'}:
        if any(arg.width != width for arg in expression.args):
            raise ValueError('An affine operation changes width')
        left, lterms = _linear(expression.args[0])
        right, rterms = _linear(expression.args[1])
        sign = 1 if expression.op == 'bvadd' else -1
        terms = dict(lterms)
        for atom, coefficient in rterms.items():
            terms[atom] = (terms.get(atom, 0) + sign * coefficient) % modulus
            if not terms[atom]:
                del terms[atom]
        return (left + sign * right) % modulus, terms
    return 0, {expression: 1}


def affine_step(before, after):
    if before.width != after.width:
        return None
    a, left = _linear(before)
    b, right = _linear(after)
    return (b - a) % (1 << before.width) if left == right else None


def fold_recurrence(before, after):
    """Recognize a shift-or extension; recognition does not justify a read."""
    if after.op != 'bvor' or len(after.args) != 2:
        return None
    for shifted, digit in (after.args, tuple(reversed(after.args))):
        if (shifted.op == 'bvshl' and len(shifted.args) == 2
                and shifted.args[0] == before and shifted.args[1].op == 'bits'
                and digit.op == 'zero_extend' and len(digit.args) == 1
                and shifted.width == digit.width == before.width
                and shifted.args[1].value == digit.args[0].width):
            return {'kind': 'shift_or_digit', 'word_width': before.width,
                    'digit_width': digit.args[0].width,
                    'digit': digit.args[0].to_dict()}
    return None


def _inputs(expression):
    result = {expression} if expression.op == 'input' else set()
    return result | set().union(*(_inputs(arg) for arg in expression.args))


def _integer_affine(expression):
    """Expand addition/subtraction over Z, without modular cancellation."""
    if expression.op == 'bits':
        return expression.value, {}
    if expression.op in {'bvadd', 'bvsub'}:
        left, terms = _integer_affine(expression.args[0])
        right, others = _integer_affine(expression.args[1])
        sign = 1 if expression.op == 'bvadd' else -1
        terms = dict(terms)
        for atom, value in others.items():
            terms[atom] = terms.get(atom, 0) + sign * value
            if not terms[atom]:
                del terms[atom]
        return left + sign * right, terms
    return 0, {expression: 1}


def _subtract_affine(left, right):
    constant, terms = left[0] - right[0], dict(left[1])
    for atom, coefficient in right[1].items():
        terms[atom] = terms.get(atom, 0) - coefficient
        if not terms[atom]:
            del terms[atom]
    return constant, terms


def _source_integer_affine(term, width):
    """Preserve Z constants before a cast; do not normalize them modulo width."""
    term = _strip_enclosure(term.strip())
    term = _strip_enclosure(re.sub(r'%Z\s*$', '', term))
    if re.fullmatch(r'-?[0-9]+', term):
        return int(term), {}
    positions = [position for operator in ('+', '-') for position in _top_positions(term, operator)
                 if position > 0 and not term.startswith('->', position)]
    if positions:
        position = max(positions)
        left = _source_integer_affine(term[:position], width)
        right = _source_integer_affine(term[position + 1:], width)
        if term[position] == '+':
            right = (-right[0], {a: -c for a, c in right[1].items()})
        return _subtract_affine(left, right)
    return 0, {source_z_expression(term, {}, width): 1}


def source_sum_bounds(clauses, substitutions, constants, *, width, provenance):
    """Project only 0<=a, 0<=b, a+b<2^width from exact source clauses.

    The adapter supplies its source parameter substitution. Unsupported source
    grammar supplies no bound. This projection creates no additional premise.
    """
    if not provenance:
        raise ValueError('A source sum projection needs provenance')
    nonnegative = {}
    for index, clause in enumerate(clauses):
        match = re.fullmatch(r'0\s*<=\s*([A-Za-z_][A-Za-z_0-9]*)', clause.strip())
        if match:
            nonnegative[match[1]] = index
    result = {}
    for index, clause in enumerate(clauses):
        match = re.fullmatch(r'([A-Za-z_][A-Za-z_0-9]*)\s*\+\s*'
                             r'([A-Za-z_][A-Za-z_0-9]*)\s*<\s*'
                             r'([A-Za-z_][A-Za-z_0-9]*)', clause.strip())
        if not match:
            continue
        left, right, modulus = match.groups()
        constant = constants.get(modulus, {})
        if (left not in nonnegative or right not in nonnegative
                or left not in substitutions or right not in substitutions
                or constant.get('value') != 1 << width or not constant.get('origin')):
            continue
        source_indices = [nonnegative[left], nonnegative[right], index]
        source = {'projection': provenance, 'clause_indices': source_indices,
                  'source_clauses': [clauses[i] for i in source_indices],
                  'parameter_substitution': {name: substitutions[name] for name in (left, right)},
                  'modulus': constant}
        left_term, right_term = substitutions[left], substitutions[right]
        for term in (left_term, right_term, '(' + left_term + ') + (' + right_term + ')'):
            expression = source_z_expression(term, {}, width)
            result.setdefault(expression, {'expression': expression.to_dict(),
                'minimum': 0, 'maximum': (1 << width) - 1,
                'interpretation': 'source_integer', 'integer_term': term,
                'premise': '(' + left_term + ') >= 0 /\\ (' + right_term +
                    ') >= 0 /\\ (' + left_term + ') + (' + right_term + ') < ' + str(1 << width),
                'provenance': source})
    return list(result.values())


class UnsignedCursorInduction:
    """Check unit-step induction from exact source bounds and the exit guard.

    The source supplies unsigned bounds on exact typed expressions. Each bound
    needs its original premise and provenance. A finite interval is sufficient;
    a coupled bound that this checker cannot use remains an explicit obligation.
    No supplied bound is a proof of a new machine premise.
    """

    def __init__(self, seed, source_bounds=()):
        self.seed = seed
        self.bounds = {}
        self.bindings = []
        self.integer_bounds = {}
        for row in source_bounds:
            expression = Expr.from_dict(row['expression'])
            lower, upper = row['minimum'], row['maximum']
            if (type(lower) is not int or type(upper) is not int
                    or not isinstance(expression.width, int)
                    or not 0 <= lower <= upper < 1 << expression.width
                    or not row.get('provenance') or not row.get('premise')):
                raise ValueError('A cursor bound needs a typed unsigned interval and source premise')
            if expression in self.bounds:
                raise ValueError('A cursor bound repeats an exact expression')
            self.bounds[expression] = (lower, upper)
            self.bindings.append(dict(row))
            if row.get('interpretation') == 'source_integer':
                term = row.get('integer_term')
                if not term or _source_integer_affine(term, expression.width) != _integer_affine(expression):
                    raise ValueError('A source integer bound has a different typed expression')
                self.integer_bounds[expression] = (lower, upper)
        self.guards = GuardNormalForm(seed.conditions)

    def _atom_interval(self, atom):
        lower, upper = self.guards.interval(self.guards.unsigned(atom))
        if atom in self.bounds:
            source_lower, source_upper = self.bounds[atom]
            lower, upper = max(lower, source_lower), min(upper, source_upper)
        return lower, upper

    def _interval(self, affine):
        lower = upper = affine[0]
        for atom, coefficient in affine[1].items():
            lo, hi = self._atom_interval(atom)
            lower += coefficient * (lo if coefficient >= 0 else hi)
            upper += coefficient * (hi if coefficient >= 0 else lo)
        return lower, upper

    def _normal_integer(self, term):
        if term.op == 'constant':
            return term.value, {}
        if term.op in {'add', 'sub'}:
            left, right = self._normal_integer(term.args[0]), self._normal_integer(term.args[1])
            if term.op == 'sub':
                return _subtract_affine(left, right)
            return _subtract_affine(left, (-right[0], {a: -c for a, c in right[1].items()}))
        if term.op == 'unsigned':
            return 0, {term.value: 1}
        raise ValueError('A cursor inequality has no supported unsigned integer view')

    def _normal_affine(self, expression):
        if expression.op in {'bvadd', 'bvsub'}:
            if any(child.width != expression.width for child in expression.args):
                raise ValueError('A cursor arithmetic expression changes width')
            left, right = (self._normal_affine(child) for child in expression.args)
            if expression.op == 'bvadd':
                right = (-right[0], {atom: -c for atom, c in right[1].items()})
            return _subtract_affine(left, right)
        return self._normal_integer(self.guards.unsigned(expression))

    def _direct_upper(self, affine):
        upper = self._interval(affine)[1]
        for condition in self.seed.conditions:
            relation = self.guards.relation(condition)
            if relation is None:
                continue
            op, left, right = relation
            if op in {'>', '>='}:
                op, left, right = ('<' if op == '>' else '<='), right, left
            if op not in {'<', '<=', '='}:
                continue
            try:
                constraint = _subtract_affine(self._normal_integer(left), self._normal_integer(right))
            except ValueError:
                # An unsupported signed clause remains in the source state.
                # It supplies no inequality to this unsigned checker.
                continue
            variants = [constraint]
            if op == '=':
                variants.append((-constraint[0], {a: -c for a, c in constraint[1].items()}))
            for constant, terms in variants:
                if terms == affine[1]:
                    upper = min(upper, (-1 if op == '<' else 0) + affine[0] - constant)
        return upper

    def _proven_interval(self, affine):
        negated = (-affine[0], {a: -c for a, c in affine[1].items()})
        lower, upper = -self._direct_upper(negated), self._direct_upper(affine)
        for expression, (source_lower, source_upper) in self.integer_bounds.items():
            source = self._normal_affine(expression)
            difference = _subtract_affine(affine, source)
            minus = (-difference[0], {a: -c for a, c in difference[1].items()})
            lower = max(lower, source_lower - self._direct_upper(minus))
            upper = min(upper, source_upper + self._direct_upper(difference))
        return lower, upper

    def _checked_expression(self, expression, checks):
        affine = self._normal_affine(expression)
        lower, upper = self._proven_interval(affine)
        if not 0 <= lower <= upper < 1 << expression.width:
            raise _MissingCursorRelation({'kind': 'unsigned_nonwrap',
                'expression': expression.to_dict(), 'available_interval': [lower, upper],
                'required': '0 <= integer expression < ' + str(1 << expression.width)})
        checks.append({'kind': 'unsigned_nonwrap', 'expression': expression.to_dict(),
                       'interval': [lower, upper]})
        return affine

    def __call__(self, candidate, edge, state):
        if candidate.get('kind') != 'affine_cursor':
            return {'status': 'unavailable', 'reason': 'This checker handles only cursor induction'}
        checks = []
        key = candidate['register']
        origin = Expr.from_dict(candidate['origin'])
        view = candidate.get('origin_view')
        try:
            if view is not None:
                # The public source parser checks the exact typed cast/add tree.
                parsed = source_z_expression(view['term'], {}, origin.width)
                if _source_integer_affine(view['term'], origin.width) != _integer_affine(origin):
                    raise _MissingCursorRelation({'kind': 'origin_identity',
                        'source_expression': parsed.to_dict(), 'actual_origin': origin.to_dict()})
                for atom in _integer_affine(parsed)[1]:
                    if atom.op == 'input' and atom not in self.integer_bounds:
                        raise _MissingCursorRelation({'kind': 'source_origin_range',
                            'expression': atom.to_dict(),
                            'required': 'A source Z bound that removes this exact input cast'})
                checks.append({'kind': 'origin_identity', 'source': view['provenance']})
            limit_key = candidate.get('limit_register')
            if limit_key is None:
                raise _MissingCursorRelation({'kind': 'stable_loop_endpoint',
                    'required': 'A unique unchanged endpoint in every backedge guard'})
            limit = Expr.from_dict(candidate['limit'])
            if state.registers.get(limit_key) != limit:
                raise _MissingCursorRelation({'kind': 'endpoint_identity', 'register': limit_key})
            start_poly = self._checked_expression(origin, checks)
            limit_poly = self._checked_expression(limit, checks)
            distance = _subtract_affine(limit_poly, start_poly)
            distance_bounds = self._proven_interval(distance)
            if distance_bounds[0] <= 0:
                raise _MissingCursorRelation({'kind': 'positive_loop_distance',
                    'available_interval': list(distance_bounds),
                    'required': 'unsigned initial cursor < unsigned endpoint'})
            checks.append({'kind': 'positive_loop_distance', 'interval': list(distance_bounds)})
            if edge == 'preheader':
                if state.registers.get(key) != origin:
                    raise _MissingCursorRelation({'kind': 'preheader_cursor_identity'})
                checks.append({'kind': 'preheader_i0', 'index': 0})
            else:
                before = input_expr('machine_' + key, origin.width)
                after = state.registers[key]
                if affine_step(before, after) != 1:
                    raise _MissingCursorRelation({'kind': 'backedge_unit_step',
                        'actual': after.to_dict()})
                guard_present = any(condition.op == 'not' and condition.args[0].op == '='
                    and set(condition.args[0].args) == {after, limit}
                    for condition in state.conditions)
                if not guard_present:
                    raise _MissingCursorRelation({'kind': 'backedge_exit_guard',
                        'required': 'incremented cursor differs from the same endpoint'})
                start_lower, _ = self._proven_interval(start_poly)
                _, end_upper = self._proven_interval(limit_poly)
                # These are the proposed induction hypotheses, not added source facts.
                # old<end gives old<=end-1; old+1<=end then guard gives old+1<end.
                if not 0 <= start_lower <= end_upper - 1 < (1 << origin.width) - 1:
                    raise _MissingCursorRelation({'kind': 'backedge_nonwrap',
                        'available_interval': [start_lower, end_upper - 1]})
                checks.append({'kind': 'backedge_i1', 'index': candidate['index'] + ' + 1',
                    'induction_hypotheses': [candidate['term'], candidate['lower_bound'],
                                             candidate['upper_bound']],
                    'old_cursor_interval': [start_lower, end_upper - 1],
                    'strictness': 'unit step plus exact disequality exit guard'})
            return {'status': 'checked', 'provenance': {'source_bounds': self.bindings,
                    'source_conditions': [term.to_dict() for term in self.seed.conditions]},
                    'checks': checks, 'kernel_entailment': 'OPEN'}
        except _MissingCursorRelation as missing:
            return {'status': 'failed', 'checks': checks, 'missing_relation': missing.relation}


def recheck_renderable_cursor(candidate, seed, backedges, source_bounds, *, render):
    """Recheck exact edges, then remove every individually unnecessary clause.

    The result is inclusion-minimal for this checker, not minimum cardinality.
    Original states are never changed. Source bounds stay separately bound.
    Rendering must check the complete declared scope, not syntax alone.
    """
    states = [('preheader', seed), *[
        ('backedge:' + str(index), state) for index, state in enumerate(backedges)]]
    selected, refused, rendered = {}, [], {}
    for edge, state in states:
        selected[edge] = []
        for index, condition in enumerate(state.conditions):
            try:
                text = render(condition)
                if not isinstance(text, str) or not text.strip():
                    raise ValueError('The condition has no rendered proposition')
            except ValueError as error:
                refused.append({'edge': edge, 'condition_index': index,
                    'condition': condition.to_dict(), 'reason': str(error)})
            else:
                selected[edge].append(index)
                rendered[edge, index] = text

    def run(indices):
        reduced = {}
        for edge, state in states:
            value = state.copy()
            value.conditions = [state.conditions[index] for index in indices[edge]]
            reduced[edge] = value
        checker = UnsignedCursorInduction(reduced['preheader'], source_bounds)
        return [{'edge': edge, 'check': checker(candidate, edge, reduced[edge])}
                for edge, _ in states]

    def passed(checks):
        return all(row['check'].get('status') == 'checked' for row in checks)

    checks = run(selected)
    if not passed(checks):
        return {'checked': False, 'checks': checks, 'render_refusals': refused,
                'condition_dependencies': [], 'kernel_entailments': 'OPEN'}
    # Stable deletion order gives reproducible, inclusion-minimal dependencies.
    for edge, _ in states:
        for index in list(selected[edge]):
            trial = {name: list(values) for name, values in selected.items()}
            trial[edge].remove(index)
            if passed(run(trial)):
                selected = trial
    checks = run(selected)
    essential = []
    for edge, _ in states:
        for index in selected[edge]:
            trial = {name: list(values) for name, values in selected.items()}
            trial[edge].remove(index)
            without = run(trial)
            if passed(without):
                raise ValueError('The retained condition set is not inclusion-minimal')
            essential.append({'edge': edge, 'condition_index': index,
                'failed_checks_without_condition': [row for row in without
                    if row['check'].get('status') != 'checked']})
    return {'checked': True, 'checks': checks, 'render_refusals': refused,
        'condition_dependencies': selected['preheader'],
        'edge_condition_dependencies': selected,
        'rendered_dependencies': [{'edge': edge, 'condition_index': index,
            'rendered': rendered[edge, index]} for edge, _ in states
            for index in selected[edge]],
        'minimality': 'inclusion-minimal under exact source checker; not minimum cardinality',
        'essential_condition_checks': essential,
        'source_evidence': {'source_bounds': source_bounds},
        'kernel_entailments': 'OPEN'}


class _MissingCursorRelation(Exception):
    def __init__(self, relation):
        self.relation = relation


def loop_read_window(seed, cursor, endpoint, *, source_facts, provenance, range_interface=None):
    """Select only an existing owner and its exact source length view.

    The source chain and extent link remain obligations. No range condition is
    appended to the symbolic path, and no resource or array image is created.
    """
    if cursor not in seed.registers or endpoint not in seed.registers or not provenance:
        raise ValueError('A loop read window needs source registers and provenance')
    start = seed.registers[cursor]
    owners = [region for region in seed.memory if region.ownership_id is not None
              and region.byte_array is not None and not region.uninitialized
              and _offset(start, region.base) is not None and _offset(start, region.base) >= 0]
    if len(owners) != 1:
        raise ValueError('A loop cursor has no unique source array owner')
    region = owners[0]
    lengths = [fact for fact in source_facts if fact.get('kind') == 'bounds'
               and fact.get('status') == 'supplied' and fact.get('origin')
               and fact.get('terms', {}).get('resource_id') == region.ownership_id
               and fact.get('terms', {}).get('length_view')]
    if len(lengths) != 1:
        raise ValueError('A loop array has no unique source length view')
    length = Expr.from_dict(lengths[0]['terms']['length_view'])
    if length.width != region.base.width or start.width != region.base.width:
        raise ValueError('A loop read window changes address width')
    if range_interface is not None:
        for name in ('range', 'lookup'):
            binding = range_interface.get(name, {})
            receipt = binding.get('verification_receipt', {})
            if (not re.fullmatch(r'LoopCursorRanges\.[A-Za-z_][A-Za-z_0-9]*', binding.get('declaration', ''))
                    or not binding.get('source_sha256') or not binding.get('object_sha256')
                    or receipt.get('method') != 'module_m' or receipt.get('assumptions') != []):
                raise ValueError('A loop range interface needs closed generic physical bindings')
    return {'ownership_id': region.ownership_id,
            'range_interface': range_interface,
            'address': input_expr('machine_' + cursor, start.width).to_dict(),
            'lower': start.to_dict(), 'limit': seed.registers[endpoint].to_dict(),
            'end': operation('bvadd', region.base, length).to_dict(),
            'provenance': {'loop': provenance, 'source_length': lengths[0]},
            'kernel_range_entailment': 'OPEN'}


@dataclass(frozen=True)
class FoldRule:
    """A table row binds all three verified public proof interfaces.

    References alone do not establish applicability. The caller must validate
    the exact zero, step, source-window, and range obligations on every edge.
    """
    name: str
    digit_width: int
    word_width: int
    zero: dict
    snoc: dict
    window: dict
    function: str = 'ByteWindowFold.zesu_byte_window_fold'

    def __post_init__(self):
        if not _IDENTIFIER.fullmatch(self.name):
            raise ValueError('A fold rule needs a stable identifier')
        if not 0 < self.digit_width <= self.word_width:
            raise ValueError('A fold rule has incompatible widths')
        if self.function != 'ByteWindowFold.zesu_byte_window_fold':
            raise ValueError('A fold table must use the generic byte-window interface')
        for binding in (self.zero, self.snoc, self.window):
            if (not binding.get('declaration') or not binding.get('source_sha256')
                    or not binding.get('verification_receipt')):
                raise ValueError('A fold rule lacks a verified source binding')
            if not re.fullmatch(r'(?:ZesuSsz\.Automation\.)?ByteWindowFold(?:Word)?\.[A-Za-z_][A-Za-z_0-9]*', binding['declaration']):
                raise ValueError('A fold proof must use the generic byte-window interface')
            receipt = binding['verification_receipt']
            if not isinstance(receipt, dict) or receipt.get('method') != 'module_m' or receipt.get('assumptions') != []:
                raise ValueError('A fold binding needs closed physical verification')


@dataclass
class LoopWidening:
    seed: object
    binders: list
    relations: list
    folds: list
    edge_records: list
    refusals: list
    body_results: list
    witness_plan: dict
    write_set: tuple
    fold_candidates: list = field(default_factory=list)
    zero_refutations: list = field(default_factory=list)
    owned_read_verifications: list = field(default_factory=list)

    def to_dict(self):
        return {'schema': 'source.loop-widening.v1', 'state': self.seed.to_dict(),
                'binders': self.binders, 'relations': self.relations,
                'folds': self.folds, 'fold_candidates': self.fold_candidates, 'edge_records': self.edge_records,
                'control_transfer_obligations': [{'body_result_index': index, 'source_path': list(row.path),
                    'actual_pc': row.state.registers['PC'].to_dict() if 'PC' in row.state.registers else None,
                    'refutation': 'OPEN'} for index, row in enumerate(self.body_results)
                    if row.status == 'control_transfer'],
                'refusals': self.refusals, 'zero_refutations': self.zero_refutations,
                'owned_read_verifications': self.owned_read_verifications,
                'body_results': [result.to_dict() for result in self.body_results],
                'witness_plan': self.witness_plan, 'write_set': list(self.write_set),
                'seed_ready': not self.refusals, 'kernel_entailments': 'OPEN'}


def bind_zero_read_refutation(proposal, binding):
    """Link a verified exact target without deleting paths or promoting folds.

    The body keeps its complete source state. The target's domain, head bound,
    semantic endpoint link and original width guard remain required at the
    eventual kernel entailment. A verified pure target is not a native proof.
    """
    receipt = binding.get('verification_receipt', {})
    if (binding.get('schema') != 'source.loop-zero-refutation.v1'
            or receipt.get('method') != 'module_m' or receipt.get('assumptions') != []
            or not receipt.get('path') or not receipt.get('sha256')
            or not binding.get('source_domain') or not binding.get('compiled_object_sha256')):
        raise ValueError('A zero-arm binding needs a verified exact source target')
    cursors = [row for row in proposal.relations if row['kind'] == 'affine_cursor']
    if len(cursors) != 1:
        raise ValueError('A zero-arm binding needs its checked source head bound')
    cursor = cursors[0]
    if binding.get('endpoint') != cursor['limit']:
        raise ValueError('A zero-arm target has a different source endpoint')
    guard = Expr.from_dict(binding['count_guard'])
    if guard not in proposal.seed.conditions:
        raise ValueError('A zero-arm target lacks its original source width guard')
    outside = Expr.from_dict(binding['outside'])
    matches = []
    for index, row in enumerate(proposal.body_results):
        if outside not in row.state.conditions or guard not in row.state.conditions:
            continue
        matches.append({'body_result_index': index, 'source_path': list(row.path),
            'status': 'VERIFIED_SOURCE_TARGET', 'kernel_loop_entailment': 'OPEN',
            'source_domain': binding['source_domain'], 'head_bound': cursor['upper_bound'],
            'endpoint': binding['endpoint'], 'count_guard': binding['count_guard'],
            'outside': binding['outside'], 'verification_receipt': dict(receipt),
            'compiled_object_sha256': binding['compiled_object_sha256'],
            'declaration': binding['declaration'], 'target_name': binding['target_name']})
    if not matches:
        raise ValueError('No body path contains the verified source zero-arm condition')
    proposal.zero_refutations.extend(matches)
    for fold in proposal.fold_candidates:
        for edge in fold['edges']:
            linked = [row for row in matches if row['source_path'] == edge['source_path']]
            if linked and edge['status'] == 'OPEN_PATH_REFUTATION':
                edge['status'] = 'ZERO_READ_TARGET_VERIFIED'
                edge['verified_refutation'] = linked[0]
    # Retain every original refusal as history for the dropped relation.
    for refusal in proposal.refusals:
        if refusal['relation'] == 'recurrence':
            refusal['linked_source_refutations'] = [dict(row) for row in matches]
    return matches


def bind_owned_read_target(proposal, binding):
    """Bind a verified pure lookup target without changing its owned read.

    Complete loop entailments still need the source domain and head relation.
    The original byte owner, base, value, path and range obligation stay intact.
    """
    receipt = binding.get('verification_receipt', {})
    if (binding.get('schema') != 'source.loop-owned-read.v1'
            or receipt.get('method') != 'module_m' or receipt.get('assumptions') != []
            or not receipt.get('path') or not receipt.get('sha256')
            or not binding.get('source_domain') or not binding.get('compiled_object_sha256')):
        raise ValueError('An owned-read binding needs a verified exact source target')
    cursors = [row for row in proposal.relations if row['kind'] == 'affine_cursor']
    if len(cursors) != 1 or binding.get('endpoint') != cursors[0]['limit']:
        raise ValueError('An owned-read target has a different source endpoint')
    guard = Expr.from_dict(binding['count_guard'])
    if guard not in proposal.seed.conditions:
        raise ValueError('An owned-read target lacks its original source width guard')
    matches = []
    for index, row in enumerate(proposal.body_results):
        for read_index, read in enumerate(row.state.read_obligations):
            if (read.get('kind') != 'owned_symbolic_byte_range'
                    or read.get('array') != binding.get('array')
                    or read.get('base') != binding.get('base')):
                continue
            if read.get('address') != input_expr('machine_' + cursors[0]['register'], 64).to_dict():
                continue
            if guard not in row.state.conditions:
                continue
            matches.append({'body_result_index': index, 'read_obligation_index': read_index,
                'source_path': list(row.path), 'owner': read['owner'],
                'status': 'VERIFIED_SOURCE_TARGET', 'verification_receipt': dict(receipt),
                'binding': dict(binding), 'kernel_loop_entailment': 'OPEN'})
    if not matches:
        raise ValueError('No exact owned read matches the verified source target')
    proposal.owned_read_verifications.extend(matches)
    return matches


def widen_loop_head(seed, traces, *, loop_pc, provenance, fold_table=(),
                    validate=None, origin_views=None, source_bounds=None, symbolic_read_ranges=(), instruction_pcs=None, index_name='i'):
    """Run one body pass and retain only per-edge validated relations.

    validate(candidate, edge, state) returns a source-bound check record with
    status='checked'. Missing/failed checks drop the relation. This interface
    separates a recognized recurrence from unsigned non-wrap and owned-window
    support. A checked source equation is not a kernel entailment proof.

    origin_views maps an exact initial cursor Expr to a source Z expression and
    provenance. No contract text is parsed or inferred here. The index witness
    always subtracts that initial expression from the observed cursor value.
    """
    if not provenance:
        raise ValueError('Loop widening needs source provenance')
    if not _IDENTIFIER.fullmatch(index_name):
        raise ValueError('A loop index needs a valid binder name')
    origin_views = origin_views or {}
    traces = tuple(traces)
    written = write_set(traces, seed.registers)
    if any(key not in seed.registers for key in written):
        raise ValueError('A written register has no source seed value')
    widened = seed.copy()
    widened.symbolic_read_ranges.extend(dict(row) for row in symbolic_read_ranges)
    binders = []
    for key in written:
        value = seed.registers[key]
        if not isinstance(value.width, int) or value.width <= 0:
            raise ValueError('A written register has no exact bitvector width')
        name = 'machine_' + key
        widened.registers[key] = input_expr(name, value.width)
        if key in widened.retained_registers:
            widened.retained_registers[key] = widened.registers[key]
        binders.append({'name': name, 'type': 'bv ' + str(value.width),
                        'register': key, 'role': 'free'})
    results = evaluate_block(traces, widened, instruction_pcs=instruction_pcs)
    backedges = [row for row in results if row.status == 'complete'
                 and row.state.registers.get('PC') == bits(loop_pc, seed.registers['PC'].width)]
    relations, folds, records, refusals = [], [], [], []
    if validate is None and source_bounds is not None:
        validate = UnsignedCursorInduction(seed, source_bounds)
    plan = {'input_registers': [], 'derived': [], 'pending': [], 'kernel_entailments': 'OPEN'}

    def refuse(key, relation, reason, **detail):
        refusals.append({'register': key, 'relation': relation, 'reason': reason,
                         'provenance': provenance, **detail})

    def checked(candidate):
        checks = []
        for edge, state in [('preheader', seed), *[
                ('backedge:' + str(n), row.state) for n, row in enumerate(backedges)]]:
            result = validate(candidate, edge, state) if validate else None
            row = {'edge': edge, 'index_substitution': '0' if edge == 'preheader'
                   else index_name + ' + 1', 'candidate': candidate,
                   'check': result or {'status': 'unavailable'}}
            records.append(row)
            checks.append(isinstance(result, dict) and result.get('status') == 'checked'
                          and bool(result.get('provenance')))
        return bool(checks) and all(checks)

    if any(row.state.memory != seed.memory or row.state.writes != seed.writes
           for row in backedges):
        refuse(None, 'memory', 'A backedge changes source memory; no array widening is implemented')
    if not backedges:
        refuse(None, 'loop_backedge', 'No complete source body result returns to the loop head')
    affine = []
    for binder in binders:
        key = binder['register']
        before = widened.registers[key]
        outputs = [row.state.registers[key] for row in backedges]
        if not outputs:
            continue
        steps = [affine_step(before, after) for after in outputs]
        if all(step == 1 for step in steps):
            affine.append(key)
        elif any(step is not None for step in steps):
            refuse(key, 'affine_cursor', 'The backedge steps are not all one', steps=steps)
        elif all(before not in _inputs(after) for after in outputs):
            binder['role'] = 'overwritten'
        else:
            matches = [fold_recurrence(before, after) for after in outputs]
            if all(matches):
                rows = [rule for rule in fold_table if all(
                    rule.word_width == match['word_width']
                    and rule.digit_width == match['digit_width'] for match in matches)]
                candidate = {'kind': 'fold', 'register': key, 'recurrences': matches,
                             'proof_table': [rule.name for rule in rows]}
                if len(rows) != 1:
                    refuse(key, 'fold', 'No unique verified zero/snoc/window table row',
                           candidate=candidate)
                elif checked(candidate):
                    folds.append(candidate)
                    binder['role'] = 'fold'
                else:
                    refuse(key, 'fold', 'A source-window or fold induction check failed',
                           candidate=candidate)
            else:
                refuse(key, 'recurrence', 'The backedge is neither affine nor a registered fold',
                       backedge_values=[value.to_dict() for value in outputs])
    if len(affine) == 1:
        key = affine[0]
        start = seed.registers[key]
        origin = origin_views.get(start)
        if origin is not None and (not origin.get('term') or not origin.get('provenance')):
            raise ValueError('An unsigned origin view needs exact source provenance')
        origin_term = origin['term'] if origin else '(bv_unsigned ' + start.coq() + ')'
        endpoints = []
        for row in backedges:
            after = row.state.registers[key]
            names = set()
            for condition in row.state.conditions:
                if condition.op == 'not' and condition.args[0].op == '=':
                    left, right = condition.args[0].args
                    other = right if left == after else left if right == after else None
                    if other is not None:
                        names.update(name for name, value in seed.registers.items()
                                     if name not in written and _REGISTER.fullmatch(name)
                                     and value == other and row.state.registers.get(name) == value)
            endpoints.append(names)
        common_endpoints = set.intersection(*endpoints) if endpoints else set()
        limit_key = next(iter(common_endpoints)) if len(common_endpoints) == 1 else None
        candidate = {'kind': 'affine_cursor', 'register': key,
                     'term': 'bv_unsigned machine_' + key + ' = (' + origin_term
                             + ' + ' + index_name + ')%Z',
                     'lower_bound': '(0 <= ' + index_name + ')%Z',
                     'upper_bound': 'bv_unsigned machine_' + key + ' < bv_unsigned machine_' + limit_key
                         if limit_key else None,
                     'limit_register': limit_key,
                     'limit': seed.registers[limit_key].to_dict() if limit_key else None,
                     'origin': start.to_dict(), 'origin_view': origin,
                     'index': index_name, 'step': 1,
                     'modular_checks': {'preheader_i0': affine_step(start, seed.registers[key]) == 0,
                         'backedge_i1': [affine_step(widened.registers[key], row.state.registers[key]) == 1
                                         for row in backedges]}}
        witness = '(bv_unsigned machine_' + key + ' - (' + origin_term + '))%Z'
        witness_binding = {'name': index_name, 'type': 'lvar "zesuLoopIndex" Z',
                           'expression': witness, 'source_register': key}
        if checked(candidate):
            plan['input_registers'] = [key]
            plan['derived'] = [witness_binding]
            binders.append({'name': 'machine_' + limit_key, 'type': 'bv ' + str(start.width),
                'register': limit_key, 'role': 'observed_alias',
                'source_expression': seed.registers[limit_key].to_dict(),
                'meaning_link': 'machine_' + limit_key + ' = ' + seed.registers[limit_key].coq()})
            binders.append({'name': index_name, 'type': 'lvar "zesuLoopIndex" Z',
                            'role': 'derived'})
            relations.append(candidate)
        else:
            plan['pending'].append(witness_binding)
            refuse(key, 'affine_cursor', 'Unsigned preheader/backedge induction is not established',
                   candidate=candidate, witness=witness)
    elif affine:
        refuse(None, 'shared_index', 'More than one unit-step cursor needs a checked shared-index mapping',
               registers=affine)
    # Existing selector inputs are registers/pairs only. The integer witness
    # is computed from the already observed cursor, never a branch literal.
    input_rows, witness_rows = [], []
    for binder in binders:
        if binder.get('register') is not None:
            register = binder['register']
            width = seed.registers[register].width
            input_rows.append({'kind': 'register', 'register': register, 'width': width})
            witness_rows.append({'binder': binder['name'],
                'expression': input_expr(binder['name'], width).to_dict()})
        elif binder['role'] == 'derived':
            binding = next(row for row in plan['derived'] if row['name'] == binder['name'])
            witness_rows.append({'binder': binder['name'],
                'expression': input_expr(binding['expression'], None).to_dict(),
                'derived_from': [binding['source_register']]})
    def nested(items):
        tree = {'kind': 'unit'}
        for item in reversed(items):
            tree = {'kind': 'pair', 'left': item, 'right': tree}
        return tree
    plan.update(schema='source.join-witness-plan.v1',
                ordered_binders=[binder['name'] for binder in binders],
                input=nested(input_rows), ordered_witnesses=witness_rows,
                data=nested(witness_rows))
    plan['input_registers'] = [row['register'] for row in input_rows]
    pending_folds = []
    # Preserve a reviewable candidate even when an unrefuted fault path prevents
    # retention. It is not an active relation or an accepted entry assertion.
    for binder in binders:
        key = binder.get('register')
        if key is None or not backedges:
            continue
        matches = [fold_recurrence(widened.registers[key], row.state.registers[key])
                   for row in backedges]
        recognized = [match for match in matches if match is not None]
        if not recognized:
            continue
        tables = [rule for rule in fold_table if all(rule.word_width == match['word_width']
                  and rule.digit_width == match['digit_width'] for match in recognized)]
        if len(tables) != 1:
            continue
        table = tables[0]
        candidate = {'register': key, 'status': 'OPEN',
                     'preheader_zero': seed.registers[key] == bits(0, table.word_width),
                     'zero_lemma': table.zero, 'step_lemma': table.snoc,
                     'window_lemma': table.window, 'edges': [], 'assertion': None}
        distances = [check['interval'] for record in records
                     for check in record['check'].get('checks', [])
                     if check.get('kind') == 'positive_loop_distance']
        candidate['source_count_intervals'] = distances
        width_supported = bool(distances) and all(0 <= lo <= hi <= table.word_width // table.digit_width
                                                  for lo, hi in distances)
        candidate['word_range_supported'] = width_supported
        for number, (row, match) in enumerate(zip(backedges, matches)):
            edge = {'edge': 'backedge:' + str(number), 'source_path': list(row.path)}
            if match is None:
                edge.update(status='OPEN_PATH_REFUTATION',
                            reason='This source path has no matching shift-or byte step')
            else:
                digit = Expr.from_dict(match['digit'])
                if digit.op != 'owned_array_byte':
                    edge.update(status='OPEN_SOURCE_READ', source_digit=match['digit'])
                else:
                    array, address, base = digit.args
                    reads = [read for read in row.state.read_obligations
                             if read.get('value') == digit.to_dict()]
                    edge.update(status='OPEN_RANGE_AND_LOOKUP', source_digit=digit.to_dict(),
                                range_obligations=reads)
                    if len(relations) == 1 and width_supported:
                        cursor = relations[0]
                        offset = _offset(seed.registers[cursor['register']], base)
                        if offset is not None:
                            assertion = 'bv_unsigned machine_' + key + ' = ' + table.function + \
                                ' (' + array.coq() + ') ' + str(offset) + '%nat (Z.to_nat ' + index_name + ')'
                            if candidate['assertion'] not in (None, assertion):
                                edge.update(status='OPEN_IMAGE_IDENTITY',
                                            reason='The source fold windows differ')
                            else:
                                candidate['assertion'] = assertion
                                edge['index_substitution'] = index_name + ' + 1'
            candidate['edges'].append(edge)
        pending_folds.append(candidate)
    return LoopWidening(widened, binders, relations, folds, records, refusals,
                        results, plan, written, pending_folds)
