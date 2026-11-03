"""Render source guards as propositions and retain every rewrite requirement.

This module does not execute Rocq. Later predecessor proofs check its output.
Intervals use only bitvector types, supplied scalar rows, and the same path's
conditions. A mask never supplies the range needed to remove its own wrap.
"""
from dataclasses import dataclass
import re

try:
    from .symbolic_state import Expr
except ImportError:
    from symbolic_state import Expr


@dataclass(frozen=True)
class Integer:
    op: str
    args: tuple = ()
    value: object = None

    def coq(self):
        if self.op == 'constant':
            return f'({self.value}%Z)'
        if self.op == 'source':
            return '(' + self.value + ')'
        if self.op in {'unsigned', 'signed'}:
            return '(bv_' + self.op + ' ' + self.value.coq() + ')'
        symbol = '+' if self.op == 'add' else '-'
        return '((' + self.args[0].coq() + ' ' + symbol + ' ' + self.args[1].coq() + ')%Z)'


def constant(value):
    return Integer('constant', value=value)


def arithmetic(op, left, right):
    if left.op == right.op == 'constant':
        return constant(left.value + right.value if op == 'add' else left.value - right.value)
    if right == constant(0):
        return left
    return Integer(op, (left, right))


class GuardNormalForm:
    """Compute a conservative P3a form from one alternative's true conditions.

    Scalar rows must bind an exact Expr, its Z view, an interval, and source
    provenance. The source adapter owns their domain-specific justification.
    """

    def __init__(self, conditions=(), *, scalar_ranges=()):
        self.conditions = tuple(conditions)
        self.scalar_ranges = {}
        self.bounds = {}
        self.materialized = set()
        self.rules = []
        self.requirements = []
        self.scalar_used = set()
        for condition in self.conditions:
            self._validate(condition)
        for row in scalar_ranges:
            expression = Expr.from_dict(row['expression'])
            self._validate(expression)
            if not isinstance(expression.width, int) or isinstance(expression.width, bool) or expression.width <= 0:
                raise ValueError('A scalar range needs a closed positive bitvector width')
            if not row.get('provenance') or not row.get('premise') or not isinstance(row.get('integer_term'), str):
                raise ValueError('A scalar range needs a source premise and provenance')
            lower, upper = row['lower'], row['upper_exclusive']
            if (isinstance(lower, bool) or not isinstance(lower, int) or isinstance(upper, bool)
                    or not isinstance(upper, int) or not 0 <= lower < upper <= 1 << expression.width):
                raise ValueError('A scalar range exceeds its bitvector type')
            if expression in self.scalar_ranges:
                raise ValueError('The scalar range repeats an exact expression')
            self.scalar_ranges[expression] = dict(row)
            self.bounds[Integer('source', value=row['integer_term'])] = (lower, upper - 1)
        # Interval propagation only intersects bounds. Every premise is already
        # present in this alternative. No branch is selected or imported.
        for _ in range(len(self.conditions) + 1):
            before = dict(self.bounds)
            for condition in self.conditions:
                relation = self.relation(condition)
                if relation is not None:
                    self._constrain(*relation)
            if before == self.bounds:
                break
        self.rules, self.requirements = [], []

    def _validate(self, expression):
        if expression.width is not None and (type(expression.width) is not int or expression.width <= 0):
            raise ValueError('A guard width must be a closed positive integer')
        if expression.op == 'bits' and (type(expression.value) is not int or
                not 0 <= expression.value < 1 << expression.width):
            raise ValueError('A guard literal exceeds its exact bitvector type')
        if expression.op in {'unknown_input', 'unknown_read'}:
            raise ValueError('A guard has no source binding')
        if expression.op == 'input' and ('?' in str(expression.value) or
                re.search(r'(?<!\w)_(?!\w)', str(expression.value))):
            raise ValueError('A guard input contains an unresolved source evar')
        for child in expression.args:
            self._validate(child)

    def _record(self, rule, **fields):
        row = {'rule': rule, **fields}
        if row not in self.rules:
            self.rules.append(row)

    def interval(self, term):
        if term.op == 'constant':
            return term.value, term.value
        if term in self.bounds:
            return self.bounds[term]
        if term.op in {'unsigned', 'signed'}:
            width = term.value.width
            if not isinstance(width, int) or isinstance(width, bool) or width <= 0:
                raise ValueError('A normal-form value needs a closed positive width')
            if term.op == 'unsigned':
                return 0, (1 << width) - 1
            return -(1 << (width - 1)), (1 << (width - 1)) - 1
        if term.op in {'add', 'sub'}:
            low, high = self.interval(term.args[0])
            other_low, other_high = self.interval(term.args[1])
            return (low + other_low, high + other_high) if term.op == 'add' else (low - other_high, high - other_low)
        raise ValueError('An integer view has no source interval')

    def _intersect(self, term, lower, upper):
        old_lower, old_upper = self.interval(term)
        lower, upper = max(lower, old_lower), min(upper, old_upper)
        if lower > upper:
            # An infeasible alternative remains explicit. It supplies no bounds.
            return
        if (lower, upper) != (old_lower, old_upper):
            self.bounds[term] = lower, upper

    def _constrain(self, op, left, right):
        if op in {'>', '>='}:
            return self._constrain('<' if op == '>' else '<=', right, left)
        low, high = self.interval(left)
        other_low, other_high = self.interval(right)
        if op == '=':
            self._intersect(left, other_low, other_high)
            self._intersect(right, low, high)
        elif op in {'<', '<='}:
            strict = int(op == '<')
            self._intersect(left, low, other_high - strict)
            self._intersect(right, low + strict, other_high)

    def unsigned(self, value):
        if value.width is None:
            raise ValueError('An unsigned guard view needs a bitvector type')
        if value.op == 'bits':
            return constant(value.value)
        if value in self.scalar_ranges:
            term = Integer('source', value=self.scalar_ranges[value]['integer_term'])
            self.materialized.add(term)
            self.scalar_used.add(value)
            self._record('source_unsigned_view', expression=value.to_dict(),
                         provenance=self.scalar_ranges[value]['provenance'])
            return term
        if value.op == 'zero_extend' and value.width >= value.args[0].width:
            self._record('bv_zero_extend_unsigned')
            return self.unsigned(value.args[0])
        if value.op == 'sign_extend' and value.width == value.args[0].width:
            self._record('bv_sign_extend_identity')
            return self.unsigned(value.args[0])
        if value.op == 'sign_extend' and value.width > value.args[0].width:
            viewed = self.unsigned(value.args[0])
            lower, upper = self.interval(viewed)
            if upper < 1 << (value.args[0].width - 1):
                self._record('bv_sign_extend_unsigned_nonnegative', lower=lower, upper=upper)
                return viewed
            viewed = self.signed(value.args[0])
            lower, upper = self.interval(viewed)
            if lower >= 0:
                self._record('bv_sign_extend_unsigned_nonnegative', lower=lower, upper=upper)
                return viewed
        if value.op == 'bvand' and value.args[1].op == 'bits':
            word, mask = value.args
            modulus = mask.value + 1
            if modulus > 1 and modulus & (modulus - 1) == 0:
                low = modulus.bit_length() - 1
                if low <= value.width:
                    if word.op == 'sign_extend' and word.args[0].width == low:
                        self._record('zesu_guard_mask_signed_value', width=value.width, low=low)
                        result = self.unsigned(word.args[0])
                        self.materialized.add(result)
                        return result
                    base, offset = word, 0
                    if word.op == 'bvadd' and word.args[1].op == 'bits':
                        base, offset = word.args[0], word.args[1].value
                    viewed = self.unsigned(base)
                    lower, upper = self.interval(viewed)
                    if offset < modulus and 0 <= lower + offset <= upper + offset < modulus:
                        self._record('low_mask_no_wrap', width=value.width, low=low)
                        return arithmetic('add', viewed, constant(offset))
                    if offset < modulus and modulus <= lower + offset <= upper + offset < 2 * modulus:
                        self._record('zesu_unsigned_low_mask_add_sub_modulus' if offset else
                                     'zesu_guard_low_mask_one_wrap', width=value.width, low=low,
                                     lower=lower, upper=upper, offset=offset)
                        return arithmetic('sub', viewed, constant(modulus - offset))
                    requirement = {'kind': 'missing_mask_range', 'expression': value.to_dict(),
                                   'low': low, 'available_interval': [lower, upper], 'offset': offset}
                    if requirement not in self.requirements:
                        self.requirements.append(requirement)
        term = Integer('unsigned', value=value)
        if value.op == 'array_byte':
            self.materialized.add(term)
        return term

    def signed(self, value):
        if value.op == 'bits':
            integer = value.value
            if integer >= 1 << (value.width - 1):
                integer -= 1 << value.width
            return constant(integer)
        if value.op == 'sign_extend' and value.width >= value.args[0].width:
            self._record('bv_sign_extend_signed')
            return self.signed(value.args[0])
        if value.op == 'zero_extend' and (1 << value.args[0].width) <= (1 << value.width) // 2:
            self._record('bv_zero_extend_signed', source_width=value.args[0].width,
                         target_width=value.width, closed_modulus_bound=True)
            return self.unsigned(value.args[0])
        return Integer('signed', value=value)

    def relation(self, expression, negated=False):
        if expression.op == 'not':
            return self.relation(expression.args[0], not negated)
        op = expression.op
        if op == '=' and expression.args[0].width is not None:
            left, right = map(self.unsigned, expression.args)
            relation = '='
        elif op in {'bvult', 'bvule', 'bvugt', 'bvuge', 'bvslt', 'bvsle', 'bvsgt', 'bvsge'}:
            view = self.signed if op.startswith('bvs') else self.unsigned
            left, right = map(view, expression.args)
            relation = {'lt': '<', 'le': '<=', 'gt': '>', 'ge': '>='}[op[-2:]]
            if op == 'bvslt' and right == constant(0) and left.op == 'signed':
                word = left.value
                left, right = constant(1 << (word.width - 1)), self.unsigned(word)
                relation = '<='
                self.materialized.add(right)
                self._record('zesu_guard_signed_negative', width=word.width)
        else:
            return None
        if negated:
            relation = {'=': '<>', '<>': '=', '<': '>=', '<=': '>', '>': '<=', '>=': '<'}[relation]
        return relation, left, right

    def proposition(self, expression):
        relation = self.relation(expression)
        if relation is not None:
            op, left, right = relation
            return '((' + left.coq() + ' ' + op + ' ' + right.coq() + ')%Z)'
        if expression.op == 'bool':
            return 'True' if expression.value else 'False'
        if expression.op == 'not':
            return '(~ ' + self.proposition(expression.args[0]) + ')'
        if expression.op in {'and', 'or'}:
            symbol = ' /\\ ' if expression.op == 'and' else ' \\/ '
            return '(' + symbol.join(self.proposition(child) for child in expression.args) + ')'
        return expression.coq() + ' = true'

    def render(self, expression):
        self._validate(expression)
        self.rules, self.requirements, self.materialized, self.scalar_used = [], [], set(), set()
        proposition = self.proposition(expression)
        endpoints = []
        for term in sorted(self.materialized, key=lambda item: item.coq()):
            lower, upper = self.interval(term)
            endpoints.extend(['((' + constant(lower).coq() + ' <= ' + term.coq() + ')%Z)',
                              '((' + term.coq() + ' <= ' + constant(upper).coq() + ')%Z)'])
        source_terms = []
        for expression in sorted(self.scalar_used, key=lambda value: value.coq()):
            row = self.scalar_ranges[expression]
            for key in ('source_interval', 'unsigned_equality'):
                if key in row.get('propositions', {}):
                    source_terms.append({'term': row['propositions'][key],
                        'source': row['provenance']['declaration']})
        return {'proposition': proposition, 'endpoints': list(dict.fromkeys(endpoints)),
                'rewrites': list(self.rules), 'requirements': list(self.requirements),
                'source_terms': source_terms}
