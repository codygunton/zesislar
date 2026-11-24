"""Annotation consumption in the generator (plan A6 items 5 and 6): access placements, a call row's
returned length, and the reach of a stop inside a seeded join."""
from pathlib import Path
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parent))
import symbolic_state  # noqa: E402
from boundary_guards import BoundaryRefused, annotate_reaching_stops, require_complete_boundary  # noqa: E402
from symbolic_state import MemoryRegion, SymbolicState, _Evaluator, bits, input_expr, operation  # noqa: E402

PC = 0x50


class AccessPlacement(unittest.TestCase):
    """An owned array whose extent is only its list length, read at base + (x & 7)."""

    def setUp(self):
        self.addCleanup(setattr, symbolic_state, 'ACCESS_PLACEMENTS', symbolic_state.ACCESS_PLACEMENTS)
        base = input_expr('base', 64)
        self.state = SymbolicState(registers={'PC': bits(PC, 64)}, memory=[
            MemoryRegion(base, byte_array=input_expr('arr', None), length=input_expr('length arr', None),
                         ownership_id='arr_resource')])
        self.index = operation('bvand', input_expr('x', 64), bits(7, 64))
        self.address = operation('bvadd', base, self.index)

    def read(self):
        evaluator = _Evaluator(self.state.copy(), instruction_index=PC)
        return evaluator, evaluator.memory_byte(self.address)

    def test_without_a_placement_the_read_is_unknown(self):
        symbolic_state.ACCESS_PLACEMENTS = {}
        _, value = self.read()
        self.assertEqual(value.op, 'unknown_read')

    def test_a_placement_names_the_array_and_states_the_index_range(self):
        placement = {'pc': '0050', 'array': 'arr', 'index': 'bv_unsigned (bv_and x (BV 64%N 7%Z))',
                     'scale': 1, 'offset': 0}
        symbolic_state.ACCESS_PLACEMENTS = {PC: [placement]}
        evaluator, value = self.read()
        self.assertEqual(value.op, 'owned_array_byte')
        obligation, = evaluator.state.read_obligations
        self.assertEqual(obligation['goal'], '(0 <= bv_unsigned (bv_and x (BV 64%N 7%Z)) < '
                                             'Z.of_nat (List.length (arr)))%Z')
        self.assertEqual(obligation['placement'], placement)
        # The range is a path condition of the read, as for any symbolic in-array read.
        index = operation('bvsub', self.address, input_expr('base', 64))
        self.assertIn(operation('bvult', index, input_expr('(Z_to_bv 64%N (Z.of_nat (length arr)))', 64)),
                      evaluator.state.conditions)
        # A placement at another instruction, or of another array, places nothing.
        symbolic_state.ACCESS_PLACEMENTS = {PC + 4: [placement]}
        self.assertEqual(self.read()[1].op, 'unknown_read')
        symbolic_state.ACCESS_PLACEMENTS = {PC: [dict(placement, array='other')]}
        self.assertEqual(self.read()[1].op, 'unknown_read')


class StorePlacement(unittest.TestCase):
    """A store row ({region, offset}) puts a store at the named uninitialized region's base plus offset."""

    def setUp(self):
        self.addCleanup(setattr, symbolic_state, 'ACCESS_PLACEMENTS', symbolic_state.ACCESS_PLACEMENTS)
        from resource_seed import source_z_expression
        self.base = source_z_expression('arrayListPointer s + arrayListLength s * 32', {}, 64)
        self.state = SymbolicState(registers={'PC': bits(PC, 64)}, memory=[
            MemoryRegion(self.base, length=input_expr('(cap - len) * 32', None), uninitialized=True,
                         ownership_id='spare')])
        self.address = operation('bvadd', input_expr('word_ptr', 64), operation('bvshl', input_expr('word_len', 64),
                                                                                 bits(5, 64)))

    def store(self):
        evaluator = _Evaluator(self.state.copy(), instruction_index=PC)
        return evaluator, evaluator.placed_store(self.address)

    def test_the_row_places_the_store_and_reports_the_address_claim(self):
        symbolic_state.ACCESS_PLACEMENTS = {PC: [{'pc': '0050', 'region': 'arrayListPointer s + arrayListLength s * 32',
                                                  'offset': 8}]}
        evaluator, placed = self.store()
        self.assertEqual(placed, operation('bvadd', self.base, bits(8, 64)))
        obligation, = evaluator.state.read_obligations
        self.assertEqual((obligation['kind'], obligation['status'], obligation['owner']),
                         ('placed_store_address', 'OPEN', 'spare'))

    def test_without_the_row_or_with_another_region_nothing_is_placed(self):
        symbolic_state.ACCESS_PLACEMENTS = {}
        self.assertIsNone(self.store()[1])
        symbolic_state.ACCESS_PLACEMENTS = {PC: [{'pc': '0050', 'region': 'other', 'offset': 0}]}
        self.assertIsNone(self.store()[1])

class PlacedLoadPastEnd(unittest.TestCase):
    """A trace case that puts a placed load past its array's end bound E stops only with both rows: the
    access row placing the load in the array and the supplied domain relation `base + length <= E`."""

    def setUp(self):
        self.addCleanup(setattr, symbolic_state, 'ACCESS_PLACEMENTS', symbolic_state.ACCESS_PLACEMENTS)
        base = input_expr('base', 64)
        self.state = SymbolicState(registers={'PC': bits(PC, 64)}, memory=[
            MemoryRegion(base, byte_array=input_expr('arr', None), length=input_expr('length arr', None),
                         ownership_id='arr_resource')])
        address = operation('bvadd', operation('bvadd', base, input_expr('k', 64)), bits(16, 64))
        # The trace's case of a 4-byte load ending past the end E.
        self.guard = operation('not', operation('bvsle', operation('bvadd', operation('zero_extend', address,
                                                width=128), bits(4, 128)),
                                                operation('zero_extend', input_expr('end', 64), width=128)))
        self.placement = {'pc': '0050', 'array': 'arr', 'index': 'k', 'scale': 1, 'offset': 16}

    def relation(self, bound):
        self.state.source_intervals.append({'end_bound': {'base': input_expr('base', 64).to_dict(),
                                                          'bound': input_expr(bound, 64).to_dict()},
                                            'origin': {'fixture': True}, 'fact_id': 'wellformed:end-bound-0'})

    def run_case(self):
        evaluator = _Evaluator(self.state.copy(), instruction_index=PC)
        evaluator.state.conditions.append(self.guard)
        symbolic_state._refute_placed_past_end(self.state, evaluator)
        return evaluator

    def test_without_an_access_row_the_case_stays(self):
        self.relation('end')
        symbolic_state.ACCESS_PLACEMENTS = {}
        self.assertEqual(self.run_case().status, 'complete')
        symbolic_state.ACCESS_PLACEMENTS = {PC: [dict(self.placement, array='other')]}
        self.assertEqual(self.run_case().status, 'complete')

    def test_a_relation_with_another_bound_refutes_nothing(self):
        self.relation('other_end')
        symbolic_state.ACCESS_PLACEMENTS = {PC: [self.placement]}
        self.assertEqual(self.run_case().status, 'complete')

    def test_both_rows_refute_the_case_as_an_open_obligation(self):
        self.relation('end')
        symbolic_state.ACCESS_PLACEMENTS = {PC: [self.placement]}
        evaluator = self.run_case()
        self.assertEqual(evaluator.status, 'infeasible')
        report, = [row for row in evaluator.state.reports if row['kind'] == 'placed_end_refutation']
        self.assertEqual((report['proof_status'], report['owner']), ('open', 'arr_resource'))
        self.assertTrue(report['required_rocq_guard_projection'])


class PlacedLoadAboveLow(unittest.TestCase):
    """The trace case `address = 0x40000000` (the ZisK free-input read) of a load placed at base + off + 8
    stops only with three rows: the access row, a domain relation `2^30 <= base` and a minimum `1 <= off`."""

    def setUp(self):
        self.addCleanup(setattr, symbolic_state, 'ACCESS_PLACEMENTS', symbolic_state.ACCESS_PLACEMENTS)
        base = input_expr('base', 64)
        self.state = SymbolicState(registers={'PC': bits(PC, 64)}, memory=[
            MemoryRegion(base, byte_array=input_expr('arr', None), length=input_expr('length arr', None),
                         ownership_id='arr_resource')])
        self.offset = input_expr('(Z_to_bv 64%N (call_off))', 64)
        address = operation('bvadd', operation('bvadd', base, self.offset), bits(8, 64))
        self.guard = operation('=', operation('zero_extend', address, width=128), bits(0x40000000, 128))
        self.placement = {'pc': '0050', 'array': 'arr', 'index': 'off', 'scale': 1, 'offset': 8}

    def rows(self, low=True, minimum=True):
        if low:
            self.state.source_intervals.append({'low_bound': {'base': input_expr('base', 64).to_dict(),
                                                              'minimum': 0x40000000},
                                                'origin': {'fixture': True}, 'fact_id': 'wellformed:low-bound-0'})
        if minimum:
            self.state.source_intervals.append({'offset_minimum': {'expression': self.offset.to_dict(), 'minimum': 1},
                                                'origin': {'fixture': True}, 'fact_id': 'call_result-minimum-off'})

    def run_case(self):
        evaluator = _Evaluator(self.state.copy(), instruction_index=PC)
        evaluator.state.conditions.append(self.guard)
        symbolic_state._refute_placed_below_low(self.state, evaluator)
        return evaluator

    def test_without_the_low_bound_or_the_minimum_the_case_stays(self):
        symbolic_state.ACCESS_PLACEMENTS = {PC: [self.placement]}
        self.rows(low=False)
        self.assertEqual(self.run_case().status, 'complete')
        self.setUp()
        symbolic_state.ACCESS_PLACEMENTS = {PC: [self.placement]}
        self.rows(minimum=False)
        self.assertEqual(self.run_case().status, 'complete')

    def test_without_an_access_row_the_case_stays(self):
        self.rows()
        symbolic_state.ACCESS_PLACEMENTS = {}
        self.assertEqual(self.run_case().status, 'complete')

    def test_the_rows_refute_the_case_as_an_open_obligation(self):
        self.rows()
        symbolic_state.ACCESS_PLACEMENTS = {PC: [self.placement]}
        evaluator = self.run_case()
        self.assertEqual(evaluator.status, 'infeasible')
        report, = [row for row in evaluator.state.reports if row['kind'] == 'placed_low_refutation']
        self.assertEqual((report['proof_status'], report['least_address']), ('open', 0x40000009))
        self.assertTrue(report['required_rocq_guard_projection'])
        # A constant at or above the least address is not refuted.
        self.guard = operation('=', self.guard.args[0], bits(0x40000009, 128))
        self.assertEqual(self.run_case().status, 'complete')


class SeededJoinStops(unittest.TestCase):
    def test_a_stop_inside_a_seeded_join_reaches_the_join_and_what_follows(self):
        # 16 branches to 20 and 24; 24 is a join with a seed; 24 falls into 28.
        function = {'name': 'join', 'entry': 16, 'end': 32, 'rows': [{'pc': pc} for pc in range(16, 32, 4)],
                    'blocks': [{'start': 16, 'end': 20, 'successors': [20, 24]},
                               {'start': 20, 'end': 24, 'successors': [24]},
                               {'start': 24, 'end': 28, 'successors': [28]},
                               {'start': 28, 'end': 32, 'successors': []}]}
        stop = {'reason': 'state_check', 'block_pc': hex(24), 'instruction_pc': hex(24), 'seed_pc': hex(24),
                'path': [0]}
        report = {'stops': [stop], 'boundaries': [
            {'pc': hex(16), 'alternatives': [{'predecessor_pc': None}]},
            {'pc': hex(20), 'alternatives': [{'predecessor_pc': hex(16)}]},
            {'pc': hex(24), 'alternatives': [{'predecessor_pc': hex(16)}, {'predecessor_pc': hex(20)},
                                             {'predecessor_pc': None}]},
            {'pc': hex(28), 'alternatives': []}]}
        result = annotate_reaching_stops(report, function)
        reached = {row['pc']: len(row['reaching_stops']) for row in result['boundaries']}
        self.assertEqual(reached, {hex(16): 0, hex(20): 0, hex(24): 1, hex(28): 1})
        for pc in (24, 28):
            with self.assertRaises(BoundaryRefused):
                require_complete_boundary(next(row for row in result['boundaries'] if row['pc'] == hex(pc)))


class ReturnedLength(unittest.TestCase):
    SPEC = '''Definition fillSpec `{!islaG Sigma} `{!threadG} : iProp Sigma :=
  (machine_call someMap 0
    (fun argv sp RET =>
      ∃ (n : Z),
      bv_unsigned (argv !!! 0%nat) ↦ₘ? n ∗
      RET (fun _ =>
        ∃ (out : list byte),
        bv_unsigned (argv !!! 0%nat) ↦ₘ∗ out ∗
        True)))%I.
'''

    def fixture(self, directory, length='want'):
        from resource_seed import seed_owned_resources
        origin = {'path': 'fixture.v', 'sha256': 'fixture'}
        constants = {'dst': {'value': 0x200, 'origin': origin}}
        registers = [{'id': name, 'kind': 'register', 'register': name, 'width': 64, 'value_coq': value,
                      'symbolic_witness': None}
                     for name, value in [('x1', 'ra'), ('x2', 'Z_to_bv 64 dst'), ('x10', 'Z_to_bv 64 dst')]]
        public = {'_input_sha256': 'fixture', 'source_bindings': [origin], 'assertion_tree': {
            'kind': 'exists', 'binders': [], 'components': [
                {'id': 'collection', 'kind': 'opaque', 'coq': 'reg_col (exact_regs args)'}, *registers,
                {'id': 'dest', 'kind': 'uninitialized_memory', 'original_component': 'dst ↦ₘ? ' + length,
                 'original_address_z': 'dst', 'length_original_coq': length},
                {'id': 'terminal', 'kind': 'opaque', 'coq': 'True'}]}}
        vocabulary = {'rows': [{'kind': kind, 'source_bindings': []} for kind in
                               ('owned_byte_array', 'uninitialized_stack_span', 'permission_fraction')],
                      'input_sha256': 'fixture', 'source_vocabulary': {'imports': []}}
        root = seed_owned_resources(public, entry_pc=16, vocabulary=vocabulary, constants=constants)
        state = root.state.copy()
        state.registers.update({'PC': bits(64, 64), **{'x%d' % number: bits(0, 64) for number in range(11, 18)}})
        call = {'call_site_pc': '0x14', 'return_site_pc': '0x18', 'spec': 'fillSpec', 'spec_module': 'Spec',
                'spec_source': 'Spec.v', 'arrays': [], 'stack_bytes': 0, 'output_length_source': 'fixture'}
        Path(directory, 'Spec.v').write_text(self.SPEC)
        shapes = {'collection_ownership_id': 'collection', 'rows': []}
        return {'root_seed': root, 'shapes': shapes, 'vocabulary': vocabulary, 'constants': constants}, state, call

    def test_a_call_row_names_the_length_of_the_returned_array(self):
        from call_boundary import CallRefused, call_return_seed
        with tempfile.TemporaryDirectory() as directory:
            fixture, state, call = self.fixture(directory)
            edge = {'seed_pc': '0x10', 'state': state.to_dict()}
            with self.assertRaisesRegex(CallRefused, 'does not return a sized array'):
                call_return_seed([edge], call=call, function_root=directory, **fixture)
            call['returned_lengths'] = {'0': 'other'}
            with self.assertRaisesRegex(CallRefused, 'no unwritten caller region'):
                call_return_seed([edge], call=call, function_root=directory, **fixture)
            call['returned_lengths'] = {'0': 'want'}
            seed, public_after, _ = call_return_seed([edge], call=call, function_root=directory, **fixture)
        nodes = {node['id']: node for node in public_after['assertion_tree']['components']}
        self.assertEqual(nodes['dest']['original_component'], 'dst ↦ₘ∗ call_out')
        self.assertEqual(nodes['dest_length']['coq'], '⌜(Z.of_nat (List.length call_out) = want)%Z⌝')
        region, = [region for region in seed.state.memory if region.ownership_id == 'dest']
        self.assertEqual(region.length, input_expr('want', None))
        # The spec length is its own binder: the call step gives it the whole region, no rest stays.
        self.assertNotIn('dest_call_after', nodes)

    # The callee fills a length its arguments fix (memcpy's `argv !!! 2`), a prefix of the region.
    PREFIX_SPEC = SPEC.replace('∃ (n : Z),\n      bv_unsigned (argv !!! 0%nat) ↦ₘ? n',
                               'bv_unsigned (argv !!! 0%nat) ↦ₘ? bv_unsigned (argv !!! 2%nat)')

    def test_the_unfilled_rest_of_the_named_region_stays_the_callers(self):
        from call_boundary import call_return_seed
        self.assertNotEqual(self.PREFIX_SPEC, self.SPEC)
        with tempfile.TemporaryDirectory() as directory:
            fixture, state, call = self.fixture(directory)
            Path(directory, 'Spec.v').write_text(self.PREFIX_SPEC)
            call['returned_lengths'] = {'0': 'want'}
            state.registers['x12'] = input_expr('count', 64)
            seed, public_after, _ = call_return_seed([{'seed_pc': '0x10', 'state': state.to_dict()}], call=call,
                                                     function_root=directory, **fixture)
        nodes = {node['id']: node for node in public_after['assertion_tree']['components']}
        self.assertEqual(nodes['dest']['original_component'], 'dst ↦ₘ∗ call_out')
        self.assertEqual(nodes['dest_length']['coq'], '⌜(Z.of_nat (List.length call_out) = (bv_unsigned (count)))%Z⌝')
        self.assertEqual(nodes['dest_call_after']['original_component'],
                         '(dst + (bv_unsigned (count))) ↦ₘ? (want - (bv_unsigned (count)))')
        self.assertEqual(sorted(region.ownership_id for region in seed.state.memory), ['dest', 'dest_call_after'])

    def test_a_fill_of_the_whole_region_leaves_no_rest(self):
        # The region's length is verbatim the length the arguments fix: one array, as before.
        from call_boundary import call_return_seed
        with tempfile.TemporaryDirectory() as directory:
            fixture, state, call = self.fixture(directory, length='bv_unsigned (count)')
            Path(directory, 'Spec.v').write_text(self.PREFIX_SPEC)
            call['returned_lengths'] = {'0': 'bv_unsigned (count)'}
            state.registers['x12'] = input_expr('count', 64)
            _, public_after, _ = call_return_seed([{'seed_pc': '0x10', 'state': state.to_dict()}], call=call,
                                                  function_root=directory, **fixture)
        nodes = {node['id']: node for node in public_after['assertion_tree']['components']}
        self.assertNotIn('dest_call_after', nodes)
        self.assertEqual(nodes['dest_length']['coq'],
                         '⌜(Z.of_nat (List.length call_out) = bv_unsigned (count))%Z⌝')


class ResultWords(unittest.TestCase):
    """A call row's `result_words`: a word of the returned array read as the row's value."""
    SPEC = ReturnedLength.SPEC.replace('∃ (n : Z),\n      bv_unsigned (argv !!! 0%nat) ↦ₘ? n',
                                       'bv_unsigned (argv !!! 0%nat) ↦ₘ? 16')

    def run_call(self, words, minimums=None, length='16'):
        from call_boundary import call_return_seed
        with tempfile.TemporaryDirectory() as directory:
            fixture, state, call = ReturnedLength().fixture(directory, length=length)
            Path(directory, 'Spec.v').write_text(self.SPEC)
            call['result_words'] = words
            if minimums is not None:
                call['result_minimums'] = minimums
            state.registers['x11'] = input_expr('base', 64)
            return call_return_seed([{'seed_pc': '0x10', 'state': state.to_dict()}], call=call,
                                    function_root=directory, **fixture)

    def test_the_word_is_its_value_and_the_entry_states_the_equation(self):
        self.assertNotEqual(self.SPEC, ReturnedLength.SPEC)
        seed, public_after, _ = self.run_call({'8': 'bv_unsigned {argv:1} + {fresh:off:Z}'})
        tree = public_after['assertion_tree']
        nodes = {node['id']: node for node in tree['components']}
        fact = nodes['call_result_word_8']['coq']
        self.assertTrue(fact.startswith('⌜(bv_unsigned (bv_concat 64%N ')
                        and fact.endswith(' (List.nth 8%nat call_out (BV 8%N 0%Z))) = bv_unsigned (base) + call_off)%Z⌝'),
                        fact)
        self.assertIn('call_out', fact)
        self.assertIn({'name': 'call_off', 'type': 'Z', 'expression': input_expr('call_off', None).to_dict()},
                      tree['binders'])
        link, = seed.state.word_links
        self.assertEqual((link['resource_id'], link['offset']), ('dest_call_output', 8))
        value = operation('bvadd', input_expr('base', 64), input_expr('(Z_to_bv 64%N (call_off))', 64))
        self.assertEqual(link['value'], value)
        evaluator = _Evaluator(seed.state.copy(), instruction_index=PC)
        self.assertEqual(evaluator.memory_read(bits(0x208, 64), 8), value)
        # The other word of the array stays its bytes.
        self.assertNotEqual(evaluator.memory_read(bits(0x200, 64), 8), value)

    def test_a_word_outside_the_returned_array_is_refused(self):
        from call_boundary import CallRefused
        with self.assertRaisesRegex(CallRefused, 'not a word of the returned array'):
            self.run_call({'16': 'bv_unsigned {argv:1}'})
        with self.assertRaisesRegex(CallRefused, 'unknown template'):
            self.run_call({'0': 'bv_unsigned {argv:1} + {other}'})

    def test_without_the_key_the_seed_is_unchanged(self):
        seed, public_after, _ = self.run_call({})
        self.assertEqual(seed.state.word_links, [])
        self.assertFalse(any('result_word' in node['id'] for node in public_after['assertion_tree']['components']))

    def test_a_result_minimum_is_an_entry_fact_and_a_seed_row(self):
        from call_boundary import CallRefused
        seed, public_after, _ = self.run_call({'8': 'bv_unsigned {argv:1} + {fresh:off:Z}'}, {'off': 1})
        nodes = {node['id']: node for node in public_after['assertion_tree']['components']}
        self.assertEqual(nodes['call_result_minimum_off']['coq'], '⌜(1 <= call_off)%Z⌝')
        row, = [row for row in seed.state.source_intervals if 'offset_minimum' in row]
        self.assertEqual(row['offset_minimum'], {'expression': input_expr('(Z_to_bv 64%N (call_off))', 64).to_dict(),
                                                 'minimum': 1})
        # Without the key nothing is added; a minimum of a name that is no fresh Z binder is refused.
        seed, public_after, _ = self.run_call({'8': 'bv_unsigned {argv:1} + {fresh:off:Z}'})
        self.assertFalse(any('offset_minimum' in row for row in seed.state.source_intervals))
        self.assertFalse(any('result_minimum' in node['id'] for node in public_after['assertion_tree']['components']))
        with self.assertRaisesRegex(CallRefused, 'no fresh Z binder'):
            self.run_call({'8': 'bv_unsigned {argv:1} + {fresh:off:Z}'}, {'other': 1})


class CallValueOwnedByte(unittest.TestCase):
    def test_a_symbolic_byte_read_in_a_call_value_renders_as_its_owned_lookup(self):
        from call_boundary import _coq
        from forward_resources import owned_byte_term
        from symbolic_state import Expr
        base = input_expr('base', 64)
        byte = Expr('owned_array_byte', (input_expr('arr', None), operation('bvadd', base, input_expr('k', 64)), base),
                    8, '0' * 64)
        value = operation('zero_extend', byte, width=64)
        self.assertEqual(_coq(value), '(bv_zero_extend 64%N (' + owned_byte_term(byte) + '))')
        self.assertEqual(owned_byte_term(byte), '(List.nth (Z.to_nat ((bv_unsigned (bv_add base k) - '
                                                'bv_unsigned base)%Z)) arr (BV 8%N 0%Z))')

    def test_carried_bytes_lose_their_symbolic_reads(self):
        # A byte stored before a call reaches the return seed's region as its lookup term: the seed has
        # no read obligation that would render an `owned_array_byte` (txAccessList +0x214 after +0x1f4).
        from call_boundary import _lower_owned
        from forward_resources import owned_byte_term
        from symbolic_state import Expr
        base = input_expr('base', 64)
        byte = Expr('owned_array_byte', (input_expr('arr', None), operation('bvadd', base, input_expr('k', 64)), base),
                    8, '0' * 64)
        self.assertEqual(_lower_owned(byte), input_expr(owned_byte_term(byte), 8))
        lowered = _lower_owned(operation('zero_extend', byte, width=64))
        self.assertEqual(lowered.args, (input_expr(owned_byte_term(byte), 8),))
        self.assertEqual(_lower_owned(base), base)


class OpaqueAndReturnedCall(unittest.TestCase):
    """A call row's `opaque` rows (framed, consumed, produced spec resources) and `returns` rows."""
    SPEC = '''Definition allocSpec `{!islaG Sigma} `{!threadG} : iProp Sigma :=
  (machine_call someMap 0
    (fun argv sp RET =>
      heap ∗
      token (bv_unsigned (argv !!! 1%nat)) ∗
      RET (fun rets =>
        heap ∗
        bv_unsigned (rets !!! 0%nat) ↦ₘ? sized (bv_unsigned (rets !!! 0%nat)) ∗
        ⌜bv_unsigned (rets !!! 0%nat) = 0⌝ ∗
        True)))%I.
'''
    ROWS = [{'spec': 'heap', 'use': 'framed'},
            {'spec': 'token (bv_unsigned (argv !!! 1%nat))', 'use': 'consumed', 'caller': ['token blk']},
            {'spec': 'bv_unsigned (rets !!! 0%nat) ↦ₘ? sized (bv_unsigned (rets !!! 0%nat))', 'use': 'produced'}]

    def fixture(self, directory):
        from resource_seed import seed_owned_resources
        origin = {'path': 'fixture.v', 'sha256': 'fixture'}
        constants = {'dst': {'value': 0x200, 'origin': origin}}
        registers = [{'id': name, 'kind': 'register', 'register': name, 'width': 64, 'value_coq': value,
                      'symbolic_witness': None}
                     for name, value in [('x1', 'ra'), ('x2', 'Z_to_bv 64 dst'), ('x10', 'Z_to_bv 64 dst')]]
        public = {'_input_sha256': 'fixture', 'source_bindings': [origin], 'assertion_tree': {
            'kind': 'exists', 'binders': [], 'components': [
                {'id': 'collection', 'kind': 'opaque', 'coq': 'reg_col (exact_regs args)'}, *registers,
                {'id': 'heap', 'kind': 'opaque', 'coq': 'heap'},
                {'id': 'token', 'kind': 'opaque', 'coq': 'token blk'},
                {'id': 'terminal', 'kind': 'opaque', 'coq': 'True'}]}}
        vocabulary = {'rows': [{'kind': kind, 'source_bindings': []} for kind in
                               ('owned_byte_array', 'uninitialized_stack_span', 'permission_fraction')],
                      'input_sha256': 'fixture', 'source_vocabulary': {'imports': []}}
        root = seed_owned_resources(public, entry_pc=16, vocabulary=vocabulary, constants=constants)
        state = root.state.copy()
        state.registers.update({'PC': bits(64, 64), **{'x%d' % number: bits(0, 64) for number in range(11, 18)}})
        call = {'call_site_pc': '0x14', 'return_site_pc': '0x18', 'spec': 'allocSpec', 'spec_module': 'Spec',
                'spec_source': 'Spec.v', 'arrays': [], 'stack_bytes': 0, 'output_length_source': 'fixture'}
        Path(directory, 'Spec.v').write_text(self.SPEC)
        shapes = {'collection_ownership_id': 'collection', 'rows': []}
        return {'root_seed': root, 'shapes': shapes, 'vocabulary': vocabulary, 'constants': constants}, state, call

    def run_call(self, **rows):
        from call_boundary import call_return_seed
        with tempfile.TemporaryDirectory() as directory:
            fixture, state, call = self.fixture(directory)
            call.update(rows)
            edge = {'seed_pc': '0x10', 'state': state.to_dict()}
            return call_return_seed([edge], call=call, function_root=directory, **fixture)

    def test_without_rows_the_old_refusals_stay(self):
        from call_boundary import CallRefused
        with self.assertRaisesRegex(CallRefused, 'does not ignore the returned registers'):
            self.run_call()
        with self.assertRaisesRegex(CallRefused, 'unsupported resource: heap'):
            self.run_call(returns=[{'index': 0, 'register': 'x10'}])
        with self.assertRaisesRegex(CallRefused, 'does not ignore the returned registers'):
            self.run_call(opaque=self.ROWS)

    def test_rows_frame_consume_and_produce_and_name_the_returned_register(self):
        seed, public, _ = self.run_call(opaque=self.ROWS, returns=[{'index': 0, 'register': 'x10'}])
        nodes = {node['id']: node for node in public['assertion_tree']['components']}
        self.assertIn('heap', nodes)
        self.assertNotIn('token', nodes)
        produced = nodes['call_produced_0']
        self.assertEqual((produced['kind'], produced['address_z'], produced['length_original_coq']),
                         ('uninitialized_memory', 'bv_unsigned call_x10', 'sized (bv_unsigned call_x10)'))
        self.assertIn('bv_unsigned call_x10 = 0', nodes['call_facts']['coq'])
        self.assertIn('call_x10', {binder['name'] for binder in public['assertion_tree']['binders']})
        interval, = [row for row in seed.state.source_intervals if row['fact_id'] == 'call_x10:returned-value']
        self.assertEqual((interval['minimum'], interval['maximum']), (0, 0))

    def test_a_wrong_row_is_refused(self):
        from call_boundary import CallRefused
        returns = [{'index': 0, 'register': 'x10'}]
        wrong = [dict(self.ROWS[1], caller=['token other'])] + self.ROWS[::2]
        with self.assertRaisesRegex(CallRefused, 'not one caller component: token other'):
            self.run_call(opaque=wrong, returns=returns)
        with self.assertRaisesRegex(CallRefused, 'does not hold: absent'):
            self.run_call(opaque=self.ROWS + [{'spec': 'absent', 'use': 'framed'}], returns=returns)
        with self.assertRaisesRegex(CallRefused, 'not a fresh argument register'):
            self.run_call(opaque=self.ROWS, returns=[{'index': 0, 'register': 'x1'}])


class ListHeaderCall(OpaqueAndReturnedCall):
    """A spec array whose value is an expression of one pre binder (an array list header): the caller's
    array of that value at the argument takes the returned post value."""
    SPEC = '''Definition growSpec `{!islaG Sigma} `{!threadG} : iProp Sigma :=
  (machine_call someMap 0
    (fun argv sp RET =>
      ∃ (state : ListState),
      bv_unsigned (argv !!! 0%nat) ↦ₘ∗ listHeader state ∗
      RET (fun rets =>
        ∃ outcome : Outcome,
        bv_unsigned (argv !!! 0%nat) ↦ₘ∗ listHeader (listAfter outcome) ∗
        ⌜bv_unsigned (rets !!! 0%nat) = outcomeCode outcome⌝ ∗
        True)))%I.
'''

    def fixture(self, directory):
        fixture, state, call = super().fixture(directory)
        from resource_seed import seed_owned_resources
        public = {'_input_sha256': 'fixture', 'source_bindings': [{'path': 'fixture.v', 'sha256': 'fixture'}],
                  'assertion_tree': {'kind': 'exists', 'binders': [], 'components': [
                      *[{'id': name, 'kind': 'register', 'register': name, 'width': 64, 'value_coq': value,
                         'symbolic_witness': None}
                        for name, value in [('x1', 'ra'), ('x2', 'Z_to_bv 64 dst'), ('x10', 'Z_to_bv 64 dst')]],
                      {'id': 'collection', 'kind': 'opaque', 'coq': 'reg_col (exact_regs args)'},
                      {'id': 'list', 'kind': 'byte_array', 'original_component': 'dst ↦ₘ∗ listHeader lst',
                       'address_z': 'dst', 'byte_array_expr': input_expr('listHeader lst', None).to_dict(),
                       'element_bits': 8, 'length_original_coq': '24'},
                      {'id': 'terminal', 'kind': 'opaque', 'coq': 'True'}]}}
        root = seed_owned_resources(public, entry_pc=16, vocabulary=fixture['vocabulary'],
                                    constants=fixture['constants'])
        state = root.state.copy()
        state.registers.update({'PC': bits(64, 64), **{'x%d' % number: bits(0, 64) for number in range(11, 18)}})
        call.update(spec='growSpec', returns=[{'index': 0, 'register': 'x10'}])
        return {**fixture, 'root_seed': root}, state, call

    def test_without_rows_the_old_refusals_stay(self):
        pass

    def test_rows_frame_consume_and_produce_and_name_the_returned_register(self):
        pass

    def test_a_wrong_row_is_refused(self):
        pass

    def test_the_header_array_takes_the_post_value(self):
        seed, public, _ = self.run_call(arrays=[{'binder': 'state', 'argument': 0, 'caller_value': 'lst'}])
        nodes = {node['id']: node for node in public['assertion_tree']['components']}
        self.assertEqual(nodes['list']['original_component'], 'dst ↦ₘ∗ (listHeader (listAfter (call_outcome)))')
        self.assertIn('bv_unsigned call_x10 = outcomeCode (call_outcome)', nodes['call_facts']['coq'])

    def test_another_caller_value_is_refused(self):
        from call_boundary import CallRefused
        with self.assertRaisesRegex(CallRefused, 'no unchanged caller array listHeader other'):
            self.run_call(arrays=[{'binder': 'state', 'argument': 0, 'caller_value': 'other'}])

class ProducedUnfold(OpaqueAndReturnedCall):
    """A produced row's `as`: the spec resource (an array list buffer) enters the seed as the pieces of
    its registered LithiumUnfold, which the call block proves."""
    SPEC = '''Definition allocSpec `{!islaG Sigma} `{!threadG} : iProp Sigma :=
  (machine_call someMap 0
    (fun argv sp RET =>
      RET (fun rets =>
        ∃ outcome : Outcome,
        arrayListBuffer 32 3 (listAfter outcome) ∗
        ⌜bv_unsigned (rets !!! 0%nat) = 0⌝ ∗
        True)))%I.
'''
    PIECES = [{'coq': 'arrayListPointer (listAfter outcome) ↦ₘ∗ arrayListItems (listAfter outcome)',
               'length': 'arrayListLength (listAfter outcome) * 32'},
              '(arrayListPointer (listAfter outcome) + arrayListLength (listAfter outcome) * 32) ↦ₘ? '
              '((arrayListCapacity (listAfter outcome) - arrayListLength (listAfter outcome)) * 32)',
              'altFlBlock (arrayListPointer (listAfter outcome)) (arrayListCapacity (listAfter outcome) * 32) 3']

    def test_without_rows_the_old_refusals_stay(self):
        pass

    def test_rows_frame_consume_and_produce_and_name_the_returned_register(self):
        pass

    def test_a_wrong_row_is_refused(self):
        pass

    def run_grow(self, **row):
        return self.run_call(returns=[{'index': 0, 'register': 'x10'}],
                             opaque=[{'spec': 'arrayListBuffer 32 3 (listAfter outcome)', 'use': 'produced', **row}])

    def test_the_pieces_replace_the_opaque_resource(self):
        _, public, report = self.run_grow(**{'as': self.PIECES})
        nodes = {node['id']: node for node in public['assertion_tree']['components']}
        after = '(listAfter (call_outcome))'
        self.assertEqual((nodes['call_produced_0']['kind'], nodes['call_produced_0']['address_z']),
                         ('byte_array', 'arrayListPointer ' + after))
        self.assertEqual(nodes['call_produced_1']['kind'], 'uninitialized_memory')
        self.assertEqual(nodes['call_produced_2']['coq'], 'altFlBlock (arrayListPointer %s) (arrayListCapacity %s * 32) 3'
                         % (after, after))
        self.assertNotIn('arrayListBuffer', repr(public['assertion_tree']['components']))
        self.assertEqual(report['unfolded_produced'][0]['spec'], 'arrayListBuffer 32 3 ' + after)

    def test_without_as_the_resource_stays_opaque(self):
        _, public, report = self.run_grow()
        nodes = {node['id']: node for node in public['assertion_tree']['components']}
        self.assertEqual(nodes['call_produced_0']['coq'], 'arrayListBuffer 32 3 (listAfter (call_outcome))')
        self.assertNotIn('unfolded_produced', report)

    def test_an_unregistered_unfold_is_refused(self):
        from call_boundary import CallRefused
        self.SPEC = self.SPEC.replace('arrayListBuffer', 'someBuffer')
        with self.assertRaisesRegex(CallRefused, 'someBuffer, which has no LithiumUnfold instance'):
            self.run_call(returns=[{'index': 0, 'register': 'x10'}],
                          opaque=[{'spec': 'someBuffer 32 3 (listAfter outcome)', 'use': 'produced', 'as': self.PIECES}])

class WordLinkAcrossCall(unittest.TestCase):
    """A root word link survives a call that leaves its array alone and is dropped when the spec
    replaces the array (wrong-output fix: the return seed used to drop every link)."""
    KEEP = '''Definition keepSpec `{!islaG Sigma} `{!threadG} : iProp Sigma :=
  (machine_call someMap 0
    (fun argv sp RET =>
      RET (fun _ => True)))%I.
'''
    WRITE = '''Definition writeSpec `{!islaG Sigma} `{!threadG} : iProp Sigma :=
  (machine_call someMap 0
    (fun argv sp RET =>
      ∃ (old : list byte),
      hdr ↦ₘ∗ old ∗
      RET (fun _ =>
        ∃ (new : list byte),
        hdr ↦ₘ∗ new ∗
        True)))%I.
'''

    def run_call(self, spec, arrays, next_pc=None):
        from call_boundary import call_return_seed
        from resource_seed import seed_owned_resources
        origin = {'path': 'fixture.v', 'sha256': 'fixture'}
        constants = {'dst': {'value': 0x200, 'origin': origin}, 'hdr': {'value': 0x300, 'origin': origin}}
        registers = [{'id': name, 'kind': 'register', 'register': name, 'width': 64, 'value_coq': value,
                      'symbolic_witness': None}
                     for name, value in [('x1', 'ra'), ('x2', 'Z_to_bv 64 dst'), ('x10', 'Z_to_bv 64 dst')]]
        public = {'_input_sha256': 'fixture', 'source_bindings': [origin], 'assertion_tree': {
            'kind': 'exists', 'binders': [], 'components': [
                {'id': 'collection', 'kind': 'opaque', 'coq': 'reg_col (exact_regs args)'}, *registers,
                {'id': 'hdr', 'kind': 'byte_array', 'original_component': 'hdr ↦ₘ∗ bytes', 'address_z': 'hdr',
                 'byte_array_expr': input_expr('bytes', None).to_dict(), 'element_bits': 8,
                 'length_original_coq': '8'},
                {'id': 'terminal', 'kind': 'opaque', 'coq': 'True'}]}}
        vocabulary = {'rows': [{'kind': kind, 'source_bindings': []} for kind in
                               ('owned_byte_array', 'uninitialized_stack_span', 'permission_fraction')],
                      'input_sha256': 'fixture', 'source_vocabulary': {'imports': []}}
        link = {'fact_id': 'wellformed:word-link-0', 'kind': 'word_link', 'status': 'supplied',
                'terms': {'resource_id': 'hdr', 'offset': 0, 'size': 8, 'quantity': 'q'}, 'origin': origin}
        length = {'fact_id': 'hdr:length', 'kind': 'bounds', 'status': 'supplied',
                  'terms': {'resource_id': 'hdr', 'index': 0, 'count': 8, 'coq_statement': 'length bytes = 8'},
                  'origin': origin}
        root = seed_owned_resources(public, entry_pc=16, vocabulary=vocabulary, constants=constants,
                                    facts=[link, length])
        self.assertEqual(len(root.state.word_links), 1)
        state = root.state.copy()
        state.registers.update({'PC': bits(64, 64), **{'x%d' % number: bits(0, 64) for number in range(11, 18)}})
        if next_pc is not None:
            state.registers['nextPC'] = bits(next_pc, 64)
        name = spec.split()[1]
        call = {'call_site_pc': '0x14', 'return_site_pc': '0x18', 'spec': name, 'spec_module': 'Spec',
                'spec_source': 'Spec.v', 'arrays': arrays, 'stack_bytes': 0, 'output_length_source': 'fixture'}
        with tempfile.TemporaryDirectory() as directory:
            Path(directory, 'Spec.v').write_text(spec)
            seed, _, _ = call_return_seed([{'seed_pc': '0x10', 'state': state.to_dict()}], call=call,
                                          function_root=directory, root_seed=root, vocabulary=vocabulary,
                                          shapes={'collection_ownership_id': 'collection', 'rows': []},
                                          constants=constants)
        return seed

    def test_the_link_survives_a_call_that_leaves_its_array_alone(self):
        seed = self.run_call(self.KEEP, [])
        self.assertEqual([link['fact_id'] for link in seed.state.word_links], ['wellformed:word-link-0'])

    def test_the_link_is_dropped_when_the_spec_replaces_its_array(self):
        seed = self.run_call(self.WRITE, [{'binder': 'old', 'constant': 'hdr', 'caller_value': 'bytes',
                                           'length': 8, 'length_source': 'fixture'}])
        self.assertEqual(seed.state.word_links, [])

    def test_the_next_pc_of_a_return_seed_is_the_return_site(self):
        seed = self.run_call(self.KEEP, [], next_pc=0x1000)
        self.assertEqual(seed.state.registers['nextPC'], bits(0x18, 64))


class JoinWordLinks(unittest.TestCase):
    """A join seed keeps a word link only when every incoming edge holds it identically."""

    def link(self, value):
        return {'array': input_expr('hdr', None).to_dict(), 'offset': 0, 'size': 8,
                'value': input_expr(value, 64).to_dict(), 'fact_id': 'link', 'resource_id': 'hdr'}

    def carry(self, *edges):
        from join_generalize import carry_common_word_links
        seed = type('Seed', (), {})()
        seed.state = SymbolicState(registers={})
        return carry_common_word_links([{'state': {'word_links': links}} for links in edges], seed).state.word_links

    def test_a_link_every_edge_holds_is_kept(self):
        kept, = self.carry([self.link('q')], [self.link('q')])
        self.assertEqual(kept['value'], input_expr('q', 64))

    def test_a_link_an_edge_lacks_or_changes_is_dropped(self):
        self.assertEqual(self.carry([self.link('q')], []), [])
        self.assertEqual(self.carry([self.link('q')], [self.link('r')]), [])


if __name__ == '__main__':
    unittest.main()
