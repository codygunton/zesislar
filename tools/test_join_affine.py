"""Exact affine join controls use source values, never proof-state guesses."""
from copy import deepcopy
import json
from pathlib import Path
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parent / 'block'))
from join_affine import affine_eliminate, affine_form
from symbolic_state import Expr, bits, input_expr, operation


class AffineJoinTests(unittest.TestCase):
    def fixture(self):
        data = json.loads((Path(__file__).parent / 'block/testdata/join-698c-affine.json').read_text())
        basis = {name: [Expr.from_dict(edge['basis'][name]) for edge in data['edges']]
                 for name in data['edges'][0]['basis']}
        expressions = {'x11': input_expr('machine_x11'), 'x12': input_expr('machine_x12'),
                       'input': Expr.from_dict(data['edges'][0]['basis']['input'])}
        return data, basis, expressions

    def test_all_nine_source_edges_determine_the_payload_relation(self):
        data, basis, expressions = self.fixture()
        targets = [Expr.from_dict(edge['field8']) for edge in data['edges']]
        result = affine_eliminate(targets, basis, expressions=expressions, register_names=['x11', 'x12'])
        self.assertEqual(result['status'], 'generated')
        self.assertEqual(result['coefficients'], {'x11': -1, 'x12': 1, 'input': 1})
        self.assertEqual(result['constant'], 0)
        self.assertEqual(result['edge_count'], 9)
        self.assertFalse(result['proof_established'])

    def test_register_only_solution_precedes_parameter_solutions(self):
        data, basis, expressions = self.fixture()
        targets = [Expr.from_dict(edge['field0']) for edge in data['edges']]
        result = affine_eliminate(targets, basis, expressions=expressions, register_names=['x11', 'x12'])
        self.assertEqual(result['coefficients'], {'x11': 1})

    def test_one_perturbed_edge_refuses_the_shared_relation(self):
        data, basis, expressions = self.fixture()
        targets = [Expr.from_dict(edge['field8']) for edge in data['edges']]
        targets[0] = operation('bvadd', targets[0], bits(1, 64))
        result = affine_eliminate(targets, basis, expressions=expressions, register_names=['x11', 'x12'])
        self.assertEqual(result['status'], 'refused')
        self.assertEqual(result['kind'], 'join_affine_refusal')

    def test_modular_cancellation_is_exact(self):
        value = input_expr('value')
        expr = operation('bvadd', operation('bvadd', value, bits(-16, 64)), bits(16, 64))
        self.assertEqual(affine_form(expr), affine_form(value))

    def test_rational_only_inverse_refuses(self):
        value = input_expr('value')
        result = affine_eliminate([value], {'double': [operation('bvmul', bits(2, 64), value)]},
                                  expressions={'double': input_expr('machine_double')}, register_names=['double'])
        self.assertEqual(result['status'], 'refused')

    def test_unknown_nested_memory_atom_refuses(self):
        unknown = Expr('array_byte', (Expr('unknown_input'),), 8, 0)
        value = operation('zero_extend', unknown, width=64)
        with self.assertRaisesRegex(ValueError, 'no source binding'):
            affine_form(value)

    def test_changed_width_refuses(self):
        with self.assertRaisesRegex(ValueError, 'width or edge count'):
            affine_eliminate([bits(1, 64)], {'word': [bits(1, 8)]}, expressions={'word': input_expr('word')},
                             register_names=['word'])

    def test_inputs_remain_unchanged(self):
        data, basis, expressions = self.fixture()
        before = deepcopy(basis)
        affine_eliminate([Expr.from_dict(edge['field8']) for edge in data['edges']], basis,
                         expressions=expressions, register_names=['x11', 'x12'])
        self.assertEqual(basis, before)


if __name__ == '__main__':
    unittest.main()
