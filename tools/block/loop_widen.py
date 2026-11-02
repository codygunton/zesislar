"""Propose loop-head seeds from source traces, without proving entailments.

Every syntactic register write becomes a binder. Algebraic checks are separate
from unsigned non-wrap and byte-window obligations. An unavailable check drops
its relation and records the reason; it never supplies a guessed image.
"""
from dataclasses import dataclass
import re

try:
    from .forward_design import _footprint
    from .symbolic_state import Expr, bits, evaluate_block, input_expr, parse_trace
except ImportError:
    from forward_design import _footprint
    from symbolic_state import Expr, bits, evaluate_block, input_expr, parse_trace


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

    def __post_init__(self):
        if not _IDENTIFIER.fullmatch(self.name):
            raise ValueError('A fold rule needs a stable identifier')
        if not 0 < self.digit_width <= self.word_width:
            raise ValueError('A fold rule has incompatible widths')
        for binding in (self.zero, self.snoc, self.window):
            if (not binding.get('declaration') or not binding.get('source_sha256')
                    or not binding.get('verification_receipt')):
                raise ValueError('A fold rule lacks a verified source binding')


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

    def to_dict(self):
        return {'schema': 'source.loop-widening.v1', 'state': self.seed.to_dict(),
                'binders': self.binders, 'relations': self.relations,
                'folds': self.folds, 'edge_records': self.edge_records,
                'refusals': self.refusals,
                'body_results': [result.to_dict() for result in self.body_results],
                'witness_plan': self.witness_plan, 'write_set': list(self.write_set),
                'seed_ready': not self.refusals, 'kernel_entailments': 'OPEN'}


def widen_loop_head(seed, traces, *, loop_pc, provenance, fold_table=(),
                    validate=None, origin_views=None, index_name='i'):
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
    results = evaluate_block(traces, widened)
    backedges = [row for row in results if row.status == 'complete'
                 and row.state.registers.get('PC') == bits(loop_pc, seed.registers['PC'].width)]
    relations, folds, records, refusals = [], [], [], []
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
        candidate = {'kind': 'affine_cursor', 'register': key,
                     'term': 'bv_unsigned machine_' + key + ' = (' + origin_term
                             + ' + ' + index_name + ')%Z',
                     'lower_bound': '(0 <= ' + index_name + ')%Z',
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
    return LoopWidening(widened, binders, relations, folds, records, refusals,
                        results, plan, written)
