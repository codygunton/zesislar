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
                {'id': 'dest', 'kind': 'uninitialized_memory', 'original_component': 'dst ↦ₘ? want',
                 'original_address_z': 'dst', 'length_original_coq': 'want'},
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
        self.assertEqual(nodes['dest_length']['coq'], '⌜(List.length call_out = want)%nat⌝')
        region, = [region for region in seed.state.memory if region.ownership_id == 'dest']
        self.assertEqual(region.length, input_expr('want', None))


if __name__ == '__main__':
    unittest.main()
