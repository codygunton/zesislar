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
        self.assertEqual(nodes['dest_length']['coq'], '⌜(Z.of_nat (List.length call_out) = want)%Z⌝')
        region, = [region for region in seed.state.memory if region.ownership_id == 'dest']
        self.assertEqual(region.length, input_expr('want', None))


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
