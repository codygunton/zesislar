"""Loop widening controls from frozen forward states and source traces."""
from pathlib import Path
import json
import unittest

try:
    from .forward_resource_design import _state_from_result
    from .loop_widen import FoldRule, UnsignedCursorInduction, source_sum_bounds, affine_step, fold_recurrence, widen_loop_head, write_set
    from .symbolic_state import bits, input_expr, operation
except ImportError:
    from forward_resource_design import _state_from_result
    from loop_widen import FoldRule, UnsignedCursorInduction, source_sum_bounds, affine_step, fold_recurrence, widen_loop_head, write_set
    from symbolic_state import bits, input_expr, operation


HERE = Path(__file__).parent


class LoopWidenTests(unittest.TestCase):
    def fixture(self, suffix):
        data = json.loads((HERE / 'testdata' / ('loop_widen_' + suffix + '.json')).read_text())
        traces = [row['source'] for row in data['body_traces']]
        return data, traces

    def test_conditional_write_is_in_union(self):
        for suffix in ('6a24', '6ac4'):
            data, traces = self.fixture(suffix)
            state = _state_from_result(data['preheaders'][0]['state'])
            self.assertEqual(write_set(traces, state.registers), ('x13', 'x15', 'x16'))

    def test_affine_modular_identity_and_changed_step(self):
        word = input_expr('cursor', 16)
        self.assertEqual(affine_step(word, operation('bvadd', word, bits(1, 16))), 1)
        self.assertEqual(affine_step(word, operation('bvadd', word, bits(2, 16))), 2)
        self.assertIsNone(affine_step(word, operation('bvxor', word, bits(1, 16))))
        self.assertIsNone(affine_step(word, input_expr('other', 16)))

    def test_fold_recognizer_does_not_claim_source_read(self):
        accumulator, byte = input_expr('acc', 64), input_expr('next_byte', 8)
        shifted = operation('bvshl', accumulator, bits(8, 64))
        extended = operation('zero_extend', byte, width=64)
        result = fold_recurrence(accumulator, operation('bvor', shifted, extended))
        self.assertEqual(result['digit_width'], 8)
        self.assertEqual(result['digit'], byte.to_dict())
        wrong = operation('bvshl', accumulator, bits(7, 64))
        self.assertIsNone(fold_recurrence(accumulator, operation('bvor', wrong, extended)))

    def test_missing_fold_proof_binding_refuses(self):
        with self.assertRaisesRegex(ValueError, 'verified source binding'):
            FoldRule('byte_fold', 8, 64, {}, {}, {})

    def test_actual_body_preserves_source_state_and_records_refusals(self):
        for suffix in ('6a24', '6ac4'):
            data, traces = self.fixture(suffix)
            for preheader in data['preheaders']:
                source = _state_from_result(preheader['state'])
                original = source.to_dict()
                result = widen_loop_head(source, traces, loop_pc=int(data['pc'], 0),
                    provenance={'source': data['forward_source'], 'alternative': preheader['source_index']})
                self.assertEqual(source.to_dict(), original)
                self.assertEqual(result.seed.memory, source.memory)
                self.assertEqual(result.seed.writes, source.writes)
                self.assertEqual(result.seed.conditions, source.conditions)
                self.assertEqual(result.seed.memory_disjoint, source.memory_disjoint)
                self.assertEqual(result.write_set, ('x13', 'x15', 'x16'))
                self.assertEqual({row['register']: row['type'] for row in result.binders},
                                 {'x13': 'bv 64', 'x15': 'bv 64', 'x16': 'bv 64'})
                self.assertEqual(next(row for row in result.binders if row['register'] == 'x16')['role'],
                                 'overwritten')
                self.assertFalse(result.relations)
                self.assertFalse(result.witness_plan['derived'])
                self.assertFalse(result.folds)
                fold = next(row for row in result.refusals if row['register'] == 'x13')
                self.assertEqual(fold['relation'], 'recurrence')
                recurrences = [fold_recurrence(result.seed.registers['x13'],
                               type(source.registers['x13']).from_dict(value))
                               for value in fold['backedge_values']]
                self.assertTrue(any(row and row['digit']['op'] == 'unknown_read'
                                    for row in recurrences))
                self.assertTrue(any(row is None for row in recurrences))
                self.assertTrue(any(row['register'] == 'x15' and row['relation'] == 'affine_cursor'
                                    for row in result.refusals))
                witness = result.witness_plan['pending'][0]
                self.assertEqual(witness['type'], 'lvar "zesuLoopIndex" Z')
                self.assertIn('bv_unsigned machine_x15 -', witness['expression'])
                self.assertNotEqual(witness['expression'], '0')
                self.assertEqual(result.to_dict()['kernel_entailments'], 'OPEN')

    def test_one_failed_edge_drops_relation_and_retains_record(self):
        data, traces = self.fixture('6a24')
        source = _state_from_result(data['preheaders'][0]['state'])
        origin = source.registers['x15']
        def validator(candidate, edge, state):
            return {'status': 'failed' if edge == 'backedge:0' else 'checked',
                    'provenance': {'source': 'unit_test_control_only'}}
        result = widen_loop_head(source, traces, loop_pc=int(data['pc'], 0),
            provenance={'source': 'unit_test_control_only'}, validate=validator,
            origin_views={origin: {'term': 'inPtr + 1',
                                  'provenance': {'source': 'unit_test_control_only'}}})
        self.assertFalse(result.relations)
        self.assertTrue(any(row['check']['status'] == 'failed' for row in result.edge_records))
        self.assertTrue(any(row['edge'] == 'preheader' and row['index_substitution'] == '0'
                            for row in result.edge_records))
        self.assertTrue(any(row['edge'].startswith('backedge:') and row['index_substitution'] == 'i + 1'
                            for row in result.edge_records))
        self.assertEqual(result.witness_plan['pending'][0]['expression'],
                         '(bv_unsigned machine_x15 - (inPtr + 1))%Z')
        self.assertFalse(any('bool' == row['type'] for row in result.binders))

    def test_origin_requires_source_binding(self):
        data, traces = self.fixture('6a24')
        source = _state_from_result(data['preheaders'][0]['state'])
        with self.assertRaisesRegex(ValueError, 'source provenance'):
            widen_loop_head(source, traces, loop_pc=int(data['pc'], 0), provenance={'source': 'fixture'},
                            origin_views={source.registers['x15']: {'term': 'inPtr + 1'}})

    def checked_fixture(self, *, maximum=None, origin_term=None):
        data, traces = self.fixture('6a24')
        seed = _state_from_result(data['preheaders'][0]['state'])
        root = seed.registers['x15'].args[0]
        bound = {'expression': root.to_dict(), 'minimum': 0,
                 'maximum': (1 << 64) - 10 if maximum is None else maximum,
                 'premise': 'synthetic unit-control bound, not an actual source premise',
                 'interpretation': 'source_integer', 'integer_term': 'decodeItemInputPointer args',
                 'provenance': {'source': 'unit_test_control_only'}}
        views = {seed.registers['x15']: {'term': origin_term or 'decodeItemInputPointer args + 1',
                 'provenance': {'source': 'unit_test_control_only'}}}
        result = widen_loop_head(seed, traces, loop_pc=int(data['pc'], 0),
            provenance={'source': 'unit_test_control_only'}, source_bounds=[bound],
            origin_views=views)
        return seed, bound, result

    def test_checked_unsigned_induction_retains_only_cursor(self):
        seed, bound, result = self.checked_fixture()
        self.assertEqual(len(result.relations), 1)
        self.assertEqual(result.relations[0]['register'], 'x15')
        self.assertIn('i', result.relations[0]['term'])
        self.assertEqual(result.relations[0]['limit_register'], 'x11')
        self.assertEqual(result.witness_plan['derived'][0]['expression'],
            '(bv_unsigned machine_x15 - (decodeItemInputPointer args + 1))%Z')
        self.assertTrue(all(row['check']['status'] == 'checked' for row in result.edge_records))
        self.assertFalse(result.folds)
        self.assertFalse(result.to_dict()['seed_ready'])

    def test_unsigned_induction_refuses_absent_bounds(self):
        data, traces = self.fixture('6a24')
        seed = _state_from_result(data['preheaders'][0]['state'])
        result = widen_loop_head(seed, traces, loop_pc=int(data['pc'], 0),
            provenance={'source': 'fixture'}, source_bounds=[])
        self.assertFalse(result.relations)
        self.assertTrue(any(row['check'].get('missing_relation', {}).get('kind') == 'unsigned_nonwrap'
                            for row in result.edge_records))

    def test_unsigned_induction_refuses_wraparound(self):
        seed, bound, result = self.checked_fixture(maximum=(1 << 64) - 1)
        self.assertFalse(result.relations)
        self.assertTrue(any(row['check'].get('missing_relation', {}).get('kind') == 'unsigned_nonwrap'
                            for row in result.edge_records))

    def test_unsigned_induction_refuses_changed_origin(self):
        seed, bound, result = self.checked_fixture(origin_term='decodeItemInputPointer args + 2')
        self.assertFalse(result.relations)
        self.assertTrue(all(row['check'].get('missing_relation', {}).get('kind') == 'origin_identity'
                            for row in result.edge_records))

    def test_unsigned_induction_refuses_missing_guard_and_changed_endpoint(self):
        seed, bound, result = self.checked_fixture()
        candidate = result.relations[0]
        backedge = next(row.state.copy() for row in result.body_results
            if row.status == 'complete' and row.state.registers['PC'] == seed.registers['PC'])
        checker = UnsignedCursorInduction(seed, [bound])
        backedge.conditions = [condition for condition in backedge.conditions
            if not (condition.op == 'not' and condition.args[0].op == '='
                    and backedge.registers['x15'] in condition.args[0].args)]
        check = checker(candidate, 'backedge:0', backedge)
        self.assertEqual(check['missing_relation']['kind'], 'backedge_exit_guard')
        backedge.registers['x11'] = bits(0, 64)
        check = checker(candidate, 'backedge:0', backedge)
        self.assertEqual(check['missing_relation']['kind'], 'endpoint_identity')

    def test_actual_source_sum_closes_cursor_induction_on_all_eight_classes(self):
        domain = json.loads((HERE / 'testdata/loop_widen_domain.json').read_text())
        bounds = source_sum_bounds(domain['original_layout_clauses'], domain['parameter_substitution'],
            domain['constants'], width=64, provenance={'source': domain['source_path']})
        self.assertEqual(len(bounds), 3)
        for suffix in ('6a24', '6ac4'):
            data, traces = self.fixture(suffix)
            for preheader in data['preheaders']:
                seed = _state_from_result(preheader['state'])
                views = {seed.registers['x15']: {'term': domain['parameter_substitution']['inputPointer'] + ' + 1',
                         'provenance': {'source': domain['source_path']}}}
                result = widen_loop_head(seed, traces, loop_pc=int(data['pc'], 0),
                    provenance={'source': data['forward_source']}, source_bounds=bounds, origin_views=views)
                self.assertEqual(len(result.relations), 1)
                self.assertTrue(all(row['check']['status'] == 'checked' for row in result.edge_records))
                self.assertEqual(result.relations[0]['register'], 'x15')
                self.assertFalse(result.folds)
                self.assertFalse(result.to_dict()['seed_ready'])

    def test_source_sum_missing_lower_bound_supplies_no_interval(self):
        domain = json.loads((HERE / 'testdata/loop_widen_domain.json').read_text())
        clauses = [term for term in domain['original_layout_clauses'] if term != '0 <= inputLength']
        self.assertEqual(source_sum_bounds(clauses, domain['parameter_substitution'], domain['constants'],
                         width=64, provenance={'source': domain['source_path']}), [])


if __name__ == '__main__':
    unittest.main()
