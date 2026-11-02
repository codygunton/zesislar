"""Join design controls use declarations and symbolic states, never proof states."""
from pathlib import Path
from copy import deepcopy
import json
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parent / 'block'))
from forward_design import _footprint
from join_generalize import (anti_unify, exit_pullback, generalize_registers, hull,
                             validate_edges, witness_plan)
from symbolic_state import Expr, bits, input_expr, operation


class FootprintTests(unittest.TestCase):
    def test_constant_write_does_not_read_its_destination(self):
        self.assertEqual(_footprint([['write-reg', '|x11|', 'nil', '#x01']], {'x11'}),
                         (set(), {'x11'}))

    def test_write_expression_keeps_source_reads(self):
        self.assertEqual(_footprint([['write-reg', '|x11|', 'nil', ['x12']]], {'x11', 'x12'}),
                         ({'x12'}, {'x11'}))

    def test_self_update_reads_its_destination(self):
        self.assertEqual(_footprint([['write-reg', '|x11|', 'nil', ['x11']]], {'x11'}),
                         ({'x11'}, {'x11'}))

    def test_prior_read_survives_a_write(self):
        self.assertEqual(_footprint([['read-reg', '|x11|', 'nil', 'v'],
                                     ['write-reg', '|x11|', 'nil', '#x01']], {'x11'}),
                         ({'x11'}, {'x11'}))

    def test_only_writes_common_to_every_branch_kill_liveness(self):
        branches = [['cases', 'condition', ['trace', ['write-reg', '|x11|', 'nil', '#x01']],
                     ['trace', ['read-reg', '|x12|', 'nil', 'v']]]]
        self.assertEqual(_footprint(branches, {'x11', 'x12'}), ({'x12'}, set()))


class JoinRegisterTests(unittest.TestCase):
    def test_6ae0_generalizes_only_the_two_differing_registers(self):
        fixture = json.loads((Path(__file__).parent / 'block/testdata/join-6ae0-registers.json').read_text())
        alternatives = []
        for row in fixture['alternatives']:
            alternatives.append({**row, 'state': {
                'registers': {**fixture['common_registers'], **row['registers']},
                'conditions': [fixture['conditions'][index] for index in row['condition_ids']]}})
        before = deepcopy(alternatives)
        plan = generalize_registers(alternatives, register_order=fixture['register_order'])
        self.assertEqual([b['name'] for b in plan['binders']], ['machine_x13', 'machine_x14'])
        self.assertEqual(len(plan['edges']), 17)
        self.assertTrue(validate_edges(plan))
        self.assertEqual(plan['witness_plan']['ordered_binders'], ['machine_x13', 'machine_x14'])
        self.assertEqual(plan['witness_plan']['input']['left']['register'], 'x13')
        self.assertEqual(plan['witness_plan']['input']['right']['left']['register'], 'x14')
        self.assertFalse(plan['proof_established'])
        self.assertEqual(alternatives, before)

    def test_equal_after_exact_normalization_keeps_the_value(self):
        word = input_expr('word')
        result = anti_unify([{'x': Expr('bvadd', (word, bits(0, 64)), 64)}, {'x': word}],
                            names={'x': 'machine_x'})
        self.assertEqual(result.values, {'x': word})
        self.assertEqual(result.binders, [])

    def test_width_change_refuses(self):
        with self.assertRaisesRegex(ValueError, 'one closed positive width'):
            anti_unify([{'x': bits(1, 8)}, {'x': bits(1, 64)}], names={'x': 'machine_x'})

    def test_missing_owned_value_refuses(self):
        with self.assertRaisesRegex(ValueError, 'different owned value sets'):
            anti_unify([{'x': bits(1, 64)}, {}], names={'x': 'machine_x'})

    def test_unknown_source_value_refuses(self):
        with self.assertRaisesRegex(ValueError, 'no source binding'):
            anti_unify([{'x': Expr('unknown_read', width=64)}, {'x': bits(1, 64)}],
                       names={'x': 'machine_x'})

    def test_hull_uses_direct_unsigned_binder_bounds(self):
        word = input_expr('word')
        bounded = operation('bvule', word, bits(55, 64))
        result = hull([bits(1, 64), word], [[], [bounded]], name='machine_x12')
        self.assertEqual((result['lower'], result['upper']), (0, 55))
        self.assertIn('bv_unsigned machine_x12', result['coq'])
        self.assertNotIn('Z_to_bv', result['coq'])

    def test_full_type_interval_emits_no_artificial_bound(self):
        self.assertIsNone(hull([input_expr('word')], [[]], name='machine_x12'))

    def test_unavailable_memory_witness_requires_packaging(self):
        with self.assertRaisesRegex(ValueError, 'array packaging'):
            witness_plan([{'name': 'memory_word', 'type': 'bv 64'}], register_bindings={})

    def test_order_is_declaration_order_without_a_python_reversal(self):
        result = witness_plan([{'name': 'last_register', 'type': 'bv 64'},
                               {'name': 'first_register', 'type': 'bv 8'}],
                              register_bindings={'last_register': ('x16', 64), 'first_register': ('x1', 8)})
        self.assertEqual(result['ordered_binders'], ['last_register', 'first_register'])
        self.assertEqual(result['data']['left']['binder'], 'last_register')
        self.assertEqual(result['data']['right']['left']['binder'], 'first_register')

    def test_tampered_edge_value_refuses(self):
        alternatives = [{'state': {'registers': {'x1': bits(value, 64).to_dict()}, 'conditions': []}}
                        for value in (1, 2)]
        plan = generalize_registers(alternatives, register_order=['x1'])
        plan['edges'][0]['widened_substitution']['machine_x1'] = bits(7, 64).to_dict()
        with self.assertRaisesRegex(ValueError, 'changes an owned value'):
            validate_edges(plan)

    def test_tampered_hull_certificate_refuses(self):
        alternatives = [{'state': {'registers': {'x1': bits(value, 64).to_dict()}, 'conditions': []}}
                        for value in (1, 2)]
        plan = generalize_registers(alternatives, register_order=['x1'])
        plan['relations'][0]['edge_intervals'][0] = [0, 0]
        with self.assertRaisesRegex(ValueError, 'interval certificate'):
            validate_edges(plan)


class ExitPullbackTests(unittest.TestCase):
    def test_one_image_creates_one_separate_meaning_link(self):
        exits = [{'kind': 'symbolic_return', 'return': 'return_address', 'image': 'closed_image'}] * 2
        result = exit_pullback(exits, allows={'application': 'allows args', 'source_binding': {'sha256': 'fixture'}})
        self.assertEqual(result['status'], 'generated')
        self.assertEqual(result['image'], 'closed_image')
        self.assertFalse(result['proof_established'])

    def test_different_images_refuse_instead_of_selecting_a_path(self):
        result = exit_pullback([{'kind': 'symbolic_return', 'image': 'a'},
                                {'kind': 'symbolic_return', 'image': 'b'}], allows={})
        self.assertEqual(result['status'], 'refused')

    def test_nonreturn_exit_refuses(self):
        self.assertEqual(exit_pullback([{'kind': 'outside_pc'}], allows={})['status'], 'refused')

if __name__ == '__main__':
    unittest.main()
