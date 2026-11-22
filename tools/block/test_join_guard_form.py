"""Profile key `join_guard_form`: how a join's edge-guard disjunction is rendered."""
from pathlib import Path
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parent))
from entry_formatter import SymbolicConditions
from join_generalize import edge_guard_disjunction, factored_guard_disjunction, join_guard_fact
from symbolic_state import input_expr, operation
import entry_hist


A, B = input_expr('machine_x10', 64), input_expr('machine_x11', 64)
COMMON = operation('=', input_expr('machine_x12', 64), input_expr('machine_x13', 64))
BELOW, ABOVE = operation('bvult', A, B), operation('bvuge', A, B)


def edge(predecessor, own):
    return {'predecessor_pc': predecessor, 'seed_pc': 0x40,
            'state': {'conditions': [COMMON.to_dict(), own.to_dict()]}}


EDGES = [edge(0x10, BELOW), edge(0x20, ABOVE)]


def atoms(expression):
    if expression.op in {'or', 'and'}:
        return sum(atoms(arg) for arg in expression.args)
    return 1


def evaluate(expression, value):
    if expression.op == 'or':
        return any(evaluate(arg, value) for arg in expression.args)
    if expression.op == 'and':
        return all(evaluate(arg, value) for arg in expression.args)
    if expression.op == 'not':
        return not evaluate(expression.args[0], value)
    return value[expression]


def rendered(condition):
    conditions = SymbolicConditions(lambda context: {'source': 'test'})
    context = {'binders': [{'name': 'machine_x10', 'type': 'bv 64'}, {'name': 'machine_x11', 'type': 'bv 64'}]}
    return [term['term']['value'] for term in conditions(condition.to_dict(), context)['components'][0]['terms']]


class JoinGuardForm(unittest.TestCase):
    def configure(self, **keys):
        entry_hist.configure({'entry_hist': 'wrap', **keys})
        self.addCleanup(entry_hist.configure, {'entry_hist': 'wrap'})

    def test_both_renders_both_halves(self):
        self.configure(join_guard_form='both')
        fact = join_guard_fact(EDGES, [COMMON])
        self.assertEqual(fact, edge_guard_disjunction(EDGES, [COMMON]))
        self.assertEqual(fact, operation('or', BELOW, ABOVE))
        terms = rendered(fact)
        self.assertEqual(terms[0], fact.coq() + ' = true')
        self.assertIn(' \\/ ', terms[1])
        self.assertEqual(rendered(join_guard_fact(EDGES, [COMMON])), rendered(operation('or', BELOW, ABOVE)))

    def test_factored_is_the_default(self):
        self.configure()
        self.assertEqual(entry_hist.JOIN_GUARD_FORM, 'factored')
        fact = join_guard_fact(EDGES, [COMMON])
        self.assertEqual(fact.coq(), operation('or', BELOW, ABOVE).coq())
        self.assertTrue(all('orb' not in term and 'bool_decide' not in term for term in rendered(fact)))

    def test_factored_chain_is_linear_and_equivalent(self):
        # A compare chain: edge k leaves after k equal bytes and one unequal byte (set C's shape).
        self.configure()
        width = 8
        equal = [operation('=', input_expr('left%d' % k, 64), input_expr('right%d' % k, 64)) for k in range(width)]
        edges = [{'predecessor_pc': 0x10 + 4 * k, 'seed_pc': 0x40, 'state': {'conditions':
                  [COMMON.to_dict(), *(g.to_dict() for g in equal[:k]), operation('not', equal[k]).to_dict()]}}
                 for k in range(width)]
        flat = edge_guard_disjunction(edges, [COMMON])
        factored = join_guard_fact(edges, [COMMON])
        self.assertEqual(factored.coq(), factored_guard_disjunction(edges, [COMMON]).coq())
        self.assertEqual(atoms(flat), width * (width + 1) // 2)
        self.assertEqual(atoms(factored), 2 * width - 1)
        for bits in range(2 ** width):
            value = {equal[k]: bool(bits >> k & 1) for k in range(width)}
            self.assertEqual(evaluate(flat, value), evaluate(factored, value))
        self.assertEqual(factored.op, 'or')
        self.assertEqual(factored.args[0], operation('not', equal[0]))
        self.assertEqual(factored.args[1].args[0], equal[0])

    def test_factored_prefix_absorbs_a_longer_path(self):
        self.configure()
        edges = [edge(0x10, BELOW), {'predecessor_pc': 0x20, 'seed_pc': 0x40, 'state': {'conditions':
                 [COMMON.to_dict(), BELOW.to_dict(), operation('=', A, B).to_dict()]}}, edge(0x30, ABOVE)]
        self.assertEqual(factored_guard_disjunction(edges, [COMMON]), operation('or', BELOW, ABOVE))

    def test_prop_drops_exactly_the_boolean_half(self):
        both = rendered(operation('or', BELOW, ABOVE))
        self.configure(join_guard_form='prop')
        fact = join_guard_fact(EDGES, [COMMON])
        self.assertEqual(fact.coq(), operation('or', BELOW, ABOVE).coq())
        self.assertEqual(rendered(fact), both[1:])
        self.assertTrue(all('orb' not in term and 'bool_decide' not in term for term in rendered(fact)))

    def test_prop_leaves_other_guards_alone(self):
        self.configure(join_guard_form='prop')
        self.assertEqual(rendered(BELOW)[0], BELOW.coq() + ' = true')
        self.assertEqual(rendered(operation('or', BELOW, ABOVE))[0], operation('or', BELOW, ABOVE).coq() + ' = true')

    def test_none_adds_no_fact(self):
        self.configure(join_guard_form='none')
        self.assertIsNotNone(edge_guard_disjunction(EDGES, [COMMON]))
        self.assertIsNone(join_guard_fact(EDGES, [COMMON]))

    def test_an_unknown_value_is_refused(self):
        self.addCleanup(entry_hist.configure, {'entry_hist': 'wrap'})
        with self.assertRaisesRegex(ValueError, 'join_guard_form: unknown value bool'):
            entry_hist.configure({'entry_hist': 'wrap', 'join_guard_form': 'bool'})


if __name__ == '__main__':
    unittest.main()
