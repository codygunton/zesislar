"""Loop widening controls from frozen forward states and source traces."""
from pathlib import Path
import json
import hashlib
import unittest

try:
    from .forward_resource_design import _state_from_result
    from .loop_widen import FoldRule, UnsignedCursorInduction, recheck_renderable_cursor, source_sum_bounds, loop_read_window, bind_zero_read_refutation, bind_owned_read_target, check_owned_fold_candidate, affine_step, fold_recurrence, widen_loop_head, write_set
    from .symbolic_state import bits, input_expr, operation, SymbolicState, evaluate_block
except ImportError:
    from forward_resource_design import _state_from_result
    from loop_widen import FoldRule, UnsignedCursorInduction, recheck_renderable_cursor, source_sum_bounds, loop_read_window, bind_zero_read_refutation, bind_owned_read_target, check_owned_fold_candidate, affine_step, fold_recurrence, widen_loop_head, write_set
    from symbolic_state import bits, input_expr, operation, SymbolicState, evaluate_block


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
                self.assertTrue(any(edge['status'] == 'OPEN_PATH_REFUTATION' for edge in candidate['edges']))
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

    def test_source_origin_does_not_cancel_a_whole_modulus(self):
        _, _, result = self.checked_fixture(
            origin_term='decodeItemInputPointer args + 1 + 18446744073709551616')
        self.assertFalse(result.relations)
        self.assertTrue(all(row['check'].get('missing_relation', {}).get('kind') == 'origin_identity'
                            for row in result.edge_records))

    def test_source_integer_bound_does_not_alias_a_wrapped_term(self):
        seed, bound, _ = self.checked_fixture()
        bound['integer_term'] += ' + 18446744073709551616'
        with self.assertRaisesRegex(ValueError, 'different typed expression'):
            UnsignedCursorInduction(seed, [bound])

    def test_optional_pc_check_preserves_default_source_bytes(self):
        golden = json.loads((HERE / 'testdata/loop_widen_default_body_hashes.json').read_text())
        for expected in golden['before_optional_pc_check']:
            data, traces = self.fixture(expected['loop'])
            source = _state_from_result(data['preheaders'][expected['source_index']]['state'])
            default = [row.to_dict() for row in evaluate_block(traces, source)]
            explicit_none = [row.to_dict() for row in evaluate_block(traces, source, instruction_pcs=None)]
            self.assertEqual(default, explicit_none)
            self.assertEqual(len(default), expected['result_count'])
            digest = hashlib.sha256(json.dumps(default, sort_keys=True, separators=(',', ':')).encode()).hexdigest()
            self.assertEqual(digest, expected['sha256'])

    def test_optional_pc_check_stops_before_later_trace_after_fault(self):
        source = SymbolicState(registers={'PC': bits(16, 64), 'x13': bits(7, 64)})
        traces = ['(trace (write-reg |PC| () #x0000000000000100))',
                  '(trace (write-reg |x13| () #x0000000000000000) (write-reg |PC| () #x0000000000000010))']
        default, = evaluate_block(traces, source)
        checked, = evaluate_block(traces, source, instruction_pcs=[16, 20])
        self.assertEqual(default.state.registers['PC'], bits(16, 64))
        self.assertEqual(default.state.registers['x13'], bits(0, 64))
        self.assertEqual(checked.status, 'control_transfer')
        self.assertEqual(checked.state.registers['PC'], bits(256, 64))
        self.assertEqual(checked.state.registers['x13'], source.registers['x13'])
        self.assertEqual(checked.state.reports[-1]['refutation'], 'OPEN')
        self.assertEqual(checked.state.reports[-1]['expected_pc'], 20)
        self.assertEqual(source.registers['PC'], bits(16, 64))

    def test_optional_pc_check_changes_nothing_on_matching_flow(self):
        source = SymbolicState(registers={'PC': bits(16, 64)})
        traces = ['(trace (write-reg |PC| () #x0000000000000014))',
                  '(trace (write-reg |PC| () #x0000000000000018))']
        default, = evaluate_block(traces, source)
        checked, = evaluate_block(traces, source, instruction_pcs=[16, 20])
        self.assertEqual(default.to_dict(), checked.to_dict())
        with self.assertRaisesRegex(ValueError, 'one nonnegative source PC'):
            evaluate_block(traces, source, instruction_pcs=[16])

    def test_checked_source_body_retains_zero_read_arm_and_open_transfers(self):
        domain = json.loads((HERE / 'testdata/loop_widen_domain.json').read_text())
        for suffix in ('6a24', '6ac4'):
            data, traces = self.fixture(suffix)
            for preheader in data['preheaders']:
                seed = _state_from_result(preheader['state'])
                window = loop_read_window(seed, 'x15', 'x11', source_facts=domain['source_facts'],
                    provenance={'source': data['forward_source']})
                result = widen_loop_head(seed, traces, loop_pc=int(data['pc'], 0),
                    provenance={'source': data['forward_source']}, symbolic_read_ranges=[window],
                    instruction_pcs=[int(row['pc'], 0) for row in data['body_traces']])
                heads = [row for row in result.body_results if row.status == 'complete'
                         and row.state.registers['PC'] == seed.registers['PC']]
                reads = [row for row in heads if row.state.read_obligations]
                zero = [row for row in heads if not row.state.read_obligations]
                self.assertEqual(len(reads), 4)
                self.assertEqual(len(zero), 1)
                self.assertEqual(zero[0].state.registers['x16'], bits(0, 64))
                self.assertTrue(all(fold_recurrence(result.seed.registers['x13'],
                    row.state.registers['x13']) for row in reads))
                self.assertTrue(result.to_dict()['control_transfer_obligations'])
                self.assertTrue(all(row['refutation'] == 'OPEN'
                    for row in result.to_dict()['control_transfer_obligations']))
                self.assertFalse(result.to_dict()['seed_ready'])

    def test_source_pc_cannot_wrap_to_match(self):
        source = SymbolicState(registers={'PC': bits(0, 8)})
        with self.assertRaisesRegex(ValueError, 'does not fit'):
            evaluate_block(['(trace)'], source, instruction_pcs=[256])

    def test_verified_zero_targets_link_without_deleting_body_states(self):
        domain = json.loads((HERE / 'testdata/loop_widen_domain.json').read_text())
        table = FoldRule(**json.loads((HERE / 'testdata/loop_widen_fold_table.json').read_text()))
        targets = json.loads((HERE / 'testdata/loop_widen_zero_refutations.json').read_text())
        read_targets = json.loads((HERE / 'testdata/loop_widen_owned_reads.json').read_text())
        bounds = source_sum_bounds(domain['original_layout_clauses'], domain['parameter_substitution'],
            domain['constants'], width=64, provenance={'source': domain['source_path']})
        for suffix in ('6a24', '6ac4'):
            data, traces = self.fixture(suffix)
            for preheader in data['preheaders']:
                source = _state_from_result(preheader['state'])
                window = loop_read_window(source, 'x15', 'x11', source_facts=domain['source_facts'],
                    provenance={'source': data['forward_source']})
                views = {source.registers['x15']: {'term': domain['parameter_substitution']['inputPointer'] + ' + 1',
                         'provenance': {'source': domain['source_path']}}}
                result = widen_loop_head(source, traces, loop_pc=int(data['pc'], 0),
                    provenance={'source': data['forward_source']}, source_bounds=bounds, origin_views=views,
                    symbolic_read_ranges=[window], fold_table=[table],
                    instruction_pcs=[int(row['pc'], 0) for row in data['body_traces']])
                before = [row.to_dict() for row in result.body_results]
                binding = next(row for row in targets if row['loop'] == suffix)
                matched = bind_zero_read_refutation(result, binding)
                # Two transfer states plus the zero arm's backedge, exit, and
                # already-infeasible branch all contain the same false guard.
                self.assertEqual(len(matched), 5)
                self.assertEqual(before, [row.to_dict() for row in result.body_results])
                self.assertTrue(any(edge['status'] == 'ZERO_READ_TARGET_VERIFIED'
                    for candidate in result.fold_candidates for edge in candidate['edges']))
                self.assertTrue(all(row['kernel_loop_entailment'] == 'OPEN' for row in matched))
                self.assertFalse(result.to_dict()['seed_ready'])
                read_binding = next(row for row in read_targets if row['loop'] == suffix)
                reads = bind_owned_read_target(result, read_binding)
                self.assertTrue(reads)
                self.assertTrue(all(row['kernel_loop_entailment'] == 'OPEN' for row in reads))
                self.assertEqual(before, [row.to_dict() for row in result.body_results])
                with self.assertRaisesRegex(ValueError, 'No exact owned read'):
                    bind_owned_read_target(result, dict(read_binding, array=input_expr('other').to_dict()))
                distance = recheck_renderable_cursor(result.relations[0], source,
                    [row.state for row in result.body_results if row.status == 'complete'
                     and row.state.registers['PC'] == bits(int(data['pc'], 0), 64)],
                    bounds, render=lambda condition: condition.coq(), required_distance_maximum=8)
                interface = json.loads((HERE / 'testdata/loop_widen_cursor_fold_interface.json').read_text())
                fold = next(row for row in result.fold_candidates if row['register'] == 'x13')
                folded = check_owned_fold_candidate(result, source, fold, distance, interface)
                self.assertTrue(folded['checked'], folded)
                self.assertEqual(folded['kernel_loop_entailment'], 'OPEN')
                self.assertFalse(result.folds)
                changed_seed = source.copy()
                changed_seed.registers['x13'] = bits(1, 64)
                self.assertFalse(check_owned_fold_candidate(result, changed_seed, fold,
                    distance, interface)['checked'])
                with self.assertRaisesRegex(ValueError, 'verified cursor-step'):
                    check_owned_fold_candidate(result, source, fold, distance,
                        dict(interface, verification_receipt={}))
                absent_zero = result.zero_refutations
                result.zero_refutations = []
                self.assertFalse(check_owned_fold_candidate(result, source, fold,
                    distance, interface)['checked'])
                result.zero_refutations = absent_zero
                absent = result.owned_read_verifications
                result.owned_read_verifications = []
                refused = check_owned_fold_candidate(result, source, fold, distance, interface)
                self.assertFalse(refused['checked'])
                result.owned_read_verifications = absent
                refused = check_owned_fold_candidate(result, source, fold,
                    dict(distance, checked=False), interface)
                self.assertFalse(refused['checked'])
                bad = dict(binding, endpoint=bits(0, 64).to_dict())
                with self.assertRaisesRegex(ValueError, 'different source endpoint'):
                    bind_zero_read_refutation(result, bad)
                bad = dict(binding, count_guard=operation('bvult', bits(0, 64), bits(1, 64)).to_dict())
                with self.assertRaisesRegex(ValueError, 'original source width guard'):
                    bind_zero_read_refutation(result, bad)

    def test_renderable_recheck_minimizes_conditions_without_mutating_states(self):
        domain = json.loads((HERE / 'testdata/loop_widen_domain.json').read_text())
        bounds = source_sum_bounds(domain['original_layout_clauses'], domain['parameter_substitution'],
            domain['constants'], width=64, provenance={'source': domain['source_path']})
        for suffix in ('6a24', '6ac4'):
            data, traces = self.fixture(suffix)
            for preheader in data['preheaders']:
                seed = _state_from_result(preheader['state'])
                views = {seed.registers['x15']: {'term': domain['parameter_substitution']['inputPointer'] + ' + 1',
                    'provenance': {'source': domain['source_path']}}}
                result = widen_loop_head(seed, traces, loop_pc=int(data['pc'], 0),
                    provenance={'source': data['forward_source']}, source_bounds=bounds, origin_views=views,
                    instruction_pcs=[int(row['pc'], 0) for row in data['body_traces']])
                edges = [row.state for row in result.body_results if row.status == 'complete'
                    and row.state.registers['PC'] == bits(int(data['pc'], 0), 64)]
                before = [state.to_dict() for state in [seed, *edges]]
                checked = recheck_renderable_cursor(result.relations[0], seed, edges, bounds,
                    render=lambda condition: condition.coq())
                self.assertTrue(checked['checked'])
                self.assertEqual(len(checked['condition_dependencies']), 2)
                self.assertTrue(all(len(values) == 1 for edge, values in
                    checked['edge_condition_dependencies'].items() if edge != 'preheader'))
                self.assertTrue(checked['render_refusals'])
                self.assertEqual(before, [state.to_dict() for state in [seed, *edges]])
                necessary = seed.conditions[checked['condition_dependencies'][0]]
                def refuse_needed(condition):
                    if condition == necessary:
                        raise ValueError('Unit control refuses one necessary condition')
                    return condition.coq()
                failed = recheck_renderable_cursor(result.relations[0], seed, edges, bounds,
                    render=refuse_needed)
                self.assertFalse(failed['checked'])
                self.assertEqual(failed['condition_dependencies'], [])
                failed = recheck_renderable_cursor(result.relations[0], seed, edges, [],
                    render=lambda condition: condition.coq())
                self.assertFalse(failed['checked'])


if __name__ == '__main__':
    unittest.main()
