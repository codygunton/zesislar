"""Profile key `join_guard_form`: how a join's edge-guard disjunction is rendered."""
from pathlib import Path
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parent))
from entry_formatter import SymbolicConditions
from join_generalize import edge_guard_disjunction, join_guard_fact
from symbolic_state import input_expr, operation
import entry_hist


A, B = input_expr('machine_x10', 64), input_expr('machine_x11', 64)
COMMON = operation('=', input_expr('machine_x12', 64), input_expr('machine_x13', 64))
BELOW, ABOVE = operation('bvult', A, B), operation('bvuge', A, B)


def edge(predecessor, own):
    return {'predecessor_pc': predecessor, 'seed_pc': 0x40,
            'state': {'conditions': [COMMON.to_dict(), own.to_dict()]}}


EDGES = [edge(0x10, BELOW), edge(0x20, ABOVE)]


def rendered(condition):
    conditions = SymbolicConditions(lambda context: {'source': 'test'})
    context = {'binders': [{'name': 'machine_x10', 'type': 'bv 64'}, {'name': 'machine_x11', 'type': 'bv 64'}]}
    return [term['term']['value'] for term in conditions(condition.to_dict(), context)['components'][0]['terms']]


class JoinGuardForm(unittest.TestCase):
    def configure(self, **keys):
        entry_hist.configure({'entry_hist': 'wrap', **keys})
        self.addCleanup(entry_hist.configure, {'entry_hist': 'wrap'})

    def test_the_default_is_both_halves(self):
        self.configure()
        self.assertEqual(entry_hist.JOIN_GUARD_FORM, 'both')
        fact = join_guard_fact(EDGES, [COMMON])
        self.assertEqual(fact, edge_guard_disjunction(EDGES, [COMMON]))
        self.assertEqual(fact, operation('or', BELOW, ABOVE))
        terms = rendered(fact)
        self.assertEqual(terms[0], fact.coq() + ' = true')
        self.assertIn(' \\/ ', terms[1])
        self.assertEqual(rendered(join_guard_fact(EDGES, [COMMON])), rendered(operation('or', BELOW, ABOVE)))

    def test_both_is_the_default(self):
        self.configure(join_guard_form='both')
        self.assertEqual(join_guard_fact(EDGES, [COMMON]), edge_guard_disjunction(EDGES, [COMMON]))

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
