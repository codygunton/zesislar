"""Loop widening controls from frozen forward states and source traces."""
from pathlib import Path
import json
import unittest

try:
    from .forward_resource_design import _state_from_result
    from .loop_widen import FoldRule, UnsignedCursorInduction, source_sum_bounds, loop_read_window, affine_step, fold_recurrence, widen_loop_head, write_set
    from .symbolic_state import bits, input_expr, operation
except ImportError:
    from forward_resource_design import _state_from_result
    from loop_widen import FoldRule, UnsignedCursorInduction, source_sum_bounds, loop_read_window, affine_step, fold_recurrence, widen_loop_head, write_set
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

    def test_loop_source_read_chain_preserves_fault_arms_and_source_owners(self):
        domain = json.loads((HERE / 'testdata/loop_widen_domain.json').read_text())
        for suffix in ('6a24', '6ac4'):
            data, traces = self.fixture(suffix)
            for preheader in data['preheaders']:
                source = _state_from_result(preheader['state'])
                window = loop_read_window(source, 'x15', 'x11', source_facts=domain['source_facts'],
                    provenance={'source': data['forward_source'], 'alternative': preheader['source_index']})
                result = widen_loop_head(source, traces, loop_pc=int(data['pc'], 0),
                    provenance={'source': data['forward_source']}, symbolic_read_ranges=[window])
                self.assertEqual(result.seed.memory, source.memory)
                self.assertEqual(result.seed.conditions, source.conditions)
                self.assertTrue(any(row.state.read_obligations for row in result.body_results))
                self.assertTrue(any(not row.state.read_obligations for row in result.body_results))
                self.assertTrue(all(obligation['owner'] == 'resource_11'
                    and obligation['status'] == 'OPEN' for row in result.body_results
                    for obligation in row.state.read_obligations))
                self.assertTrue(any('owned_array_byte' in str(row.state.registers['x13'].to_dict())
                    for row in result.body_results if 'x13' in row.state.registers))
                self.assertFalse(result.to_dict()['seed_ready'])

    def test_loop_window_refuses_missing_source_length_and_changed_owner(self):
        data, _ = self.fixture('6a24')
        source = _state_from_result(data['preheaders'][0]['state'])
        with self.assertRaisesRegex(ValueError, 'source length view'):
            loop_read_window(source, 'x15', 'x11', source_facts=[], provenance={'source': 'fixture'})
        source.registers['x15'] = input_expr('different_root', 64)
        with self.assertRaisesRegex(ValueError, 'source array owner'):
            loop_read_window(source, 'x15', 'x11', source_facts=[], provenance={'source': 'fixture'})

    def test_verified_table_candidates_keep_range_and_fault_obligations(self):
        domain = json.loads((HERE / 'testdata/loop_widen_domain.json').read_text())
        table = FoldRule(**json.loads((HERE / 'testdata/loop_widen_fold_table.json').read_text()))
        bounds = source_sum_bounds(domain['original_layout_clauses'], domain['parameter_substitution'],
            domain['constants'], width=64, provenance={'source': domain['source_path']})
        for suffix in ('6a24', '6ac4'):
            data, traces = self.fixture(suffix)
            for preheader in data['preheaders']:
                seed = _state_from_result(preheader['state'])
                window = loop_read_window(seed, 'x15', 'x11', source_facts=domain['source_facts'],
                    provenance={'source': data['forward_source']})
                views = {seed.registers['x15']: {'term': domain['parameter_substitution']['inputPointer'] + ' + 1',
                         'provenance': {'source': domain['source_path']}}}
                result = widen_loop_head(seed, traces, loop_pc=int(data['pc'], 0),
                    provenance={'source': data['forward_source']}, source_bounds=bounds,
                    origin_views=views, symbolic_read_ranges=[window], fold_table=[table])
                self.assertEqual(len(result.relations), 1)
                self.assertEqual(len(result.fold_candidates), 1)
                candidate = result.fold_candidates[0]
                self.assertTrue(candidate['preheader_zero'])
                self.assertTrue(candidate['word_range_supported'])
                self.assertTrue(all(interval == [1, 8] for interval in candidate['source_count_intervals']))
                self.assertIn('ByteWindowFold.zesu_byte_window_fold', candidate['assertion'])
                self.assertTrue(any(edge['status'] == 'OPEN_RANGE_AND_LOOKUP' for edge in candidate['edges']))
                self.assertTrue(any(edge['status'] == 'OPEN_FAULT_REFUTATION' for edge in candidate['edges']))
                self.assertFalse(result.folds)
                self.assertFalse(result.to_dict()['seed_ready'])

    def test_contract_specific_fold_reference_refuses(self):
        fields = json.loads((HERE / 'testdata/loop_widen_fold_table.json').read_text())
        fields['function'] = 'Contract.specific_fold'
        with self.assertRaisesRegex(ValueError, 'generic byte-window interface'):
            FoldRule(**fields)

    def test_range_bridge_is_bound_but_does_not_close_kernel_obligations(self):
        domain = json.loads((HERE / 'testdata/loop_widen_domain.json').read_text())
        interface = json.loads((HERE / 'testdata/loop_widen_range_interface.json').read_text())
        data, traces = self.fixture('6a24')
        seed = _state_from_result(data['preheaders'][0]['state'])
        window = loop_read_window(seed, 'x15', 'x11', source_facts=domain['source_facts'],
            provenance={'source': data['forward_source']}, range_interface=interface)
        result = widen_loop_head(seed, traces, loop_pc=int(data['pc'], 0),
            provenance={'source': data['forward_source']}, symbolic_read_ranges=[window])
        obligations = [obligation for row in result.body_results for obligation in row.state.read_obligations]
        self.assertTrue(obligations)
        self.assertTrue(all(obligation['range_interface'] == interface for obligation in obligations))
        self.assertTrue(all(obligation['status'] == 'OPEN' for obligation in obligations))
        self.assertFalse(result.to_dict()['seed_ready'])

    def test_witness_plan_covers_free_registers_and_keeps_declaration_order(self):
        _, _, result = self.checked_fixture()
        plan = result.witness_plan
        self.assertEqual(plan['schema'], 'source.join-witness-plan.v1')
        self.assertEqual(plan['ordered_binders'], [binder['name'] for binder in result.binders])
        self.assertEqual([row['binder'] for row in plan['ordered_witnesses']], plan['ordered_binders'])
        self.assertEqual(plan['input_registers'], ['x13', 'x15', 'x16', 'x11'])
        self.assertEqual(plan['ordered_witnesses'][-1]['derived_from'], ['x15'])
        self.assertIn('bv_unsigned machine_x15 -', plan['ordered_witnesses'][-1]['expression']['value'])
        self.assertEqual(result.relations[0]['upper_bound'],
                         'bv_unsigned machine_x15 < bv_unsigned machine_x11')
        alias = next(b for b in result.binders if b['role'] == 'observed_alias')
        self.assertEqual(alias['register'], 'x11')
        cursor = plan['data']
        names = []
        while cursor['kind'] == 'pair':
            names.append(cursor['left']['binder'])
            cursor = cursor['right']
        self.assertEqual(cursor, {'kind': 'unit'})
        self.assertEqual(names, plan['ordered_binders'])


if __name__ == '__main__':
    unittest.main()
