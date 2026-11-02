"""Source ownership controls write accounting and preserves every resource."""
from pathlib import Path
import hashlib
import json
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parent / 'block'))
from forward_resources import (OwnedBytes, apply_owned_writes, load_resource_vocabulary,
                               ownership_from_assertion_tree, parse_source_ownership,
                               render_resource_boundary)
from symbolic_state import Expr, MemoryRegion, MemoryWrite, SymbolicState, bits, input_expr, operation, evaluate_trace


PROVENANCE = {'source': 'entry.v', 'definition': 'entryResources'}


def owned(name='owned', base=None, length=8, *, writable=True, array=None):
    return OwnedBytes(name, base or bits(32, 64), 'original_address', array,
                      length, writable, '(DfracOwn (1%Qp))',
                      {'kind': 'unknown_byte_array', 'address': 'original_address', 'length': 'original_length'},
                      PROVENANCE, element_bits=8)


def fact(kind, **terms):
    return {'fact_id': kind + ':' + repr(terms), 'kind': kind, 'terms': terms,
            'origin': PROVENANCE, 'status': 'supplied'}


def apply(resources, writes, *, facts=(), **kwargs):
    # These fixtures supply full ownership and non-wrap facts from their seed.
    inherited = [fact('permission', resource_id=r.id, fraction=r.fraction) for r in resources]
    inherited += [fact('nonwrap', resource_id=r.id) for r in resources]
    return apply_owned_writes(resources, writes, facts=[*inherited, *facts], **kwargs)


VOCABULARY = {'input_sha256': 'source_fixture', 'source_vocabulary': {'imports': ['source.module']}}


class ForwardResourcesTests(unittest.TestCase):
    def test_source_parser_preserves_arrays_ranges_and_opaque_resources(self):
        body = '''(∃ (temporary : bv 64), reg_col inherited ∗
          "x1" ↦ᵣ RVal_Bits temporary ∗ input ↦ₘ∗ input_bytes ∗
          frame ↦ₘ? frame_length ∗ ⌜domain arguments⌝ ∗ True)%I'''
        result = parse_source_ownership(body, provenance=PROVENANCE)
        self.assertEqual(result['existential_prefixes'], ['∃ (temporary : bv 64),'])
        components = result['components']
        self.assertEqual([record['kind'] for record in components],
                         ['opaque', 'register', 'byte_array', 'unknown_byte_array', 'opaque', 'opaque'])
        self.assertEqual(components[0]['source'], 'reg_col inherited')
        self.assertEqual(components[2]['address_z'], 'input')
        self.assertEqual(components[3]['length'], 'frame_length')
        self.assertNotIn('value', components[3])
        self.assertIsNone(components[2]['writable'])
        self.assertEqual(components[4]['source'], '⌜domain arguments⌝')

    def test_source_parser_keeps_fraction_syntax_without_inferring_permission(self):
        result = parse_source_ownership('(address ↦ₘ{fraction}∗ bytes ∗ True)%I', provenance=PROVENANCE)
        memory, _ = result['components']
        self.assertEqual(memory['fraction'], '{fraction}')
        self.assertIsNone(memory['writable'])
        self.assertEqual(memory['value'], 'bytes')

    def test_comments_and_nested_conjunctions_do_not_create_components(self):
        result = parse_source_ownership('''(opaque (left ∗ right) ∗ (* hidden ↦ₘ? size ∗ *)
          address ↦ₘ∗ bytes ∗ "∗" ↦ᵣ value)%I''', provenance=PROVENANCE)
        self.assertEqual(len(result['components']), 3)
        self.assertEqual(result['components'][0]['source'], 'opaque (left ∗ right)')
        self.assertEqual(result['components'][2]['name'], '∗')

    def test_nested_or_quoted_memory_syntax_does_not_establish_ownership(self):
        result = parse_source_ownership('''(opaque "address ↦ₘ∗ bytes" ∗
          opaque (address ↦ₘ∗ bytes) ∗ (address ↦ₘ∗ bytes))%I''', provenance=PROVENANCE)
        self.assertEqual([record['kind'] for record in result['components']], ['opaque', 'opaque', 'byte_array'])

    def test_ordered_overlapping_stores_keep_the_complete_write_log(self):
        resource = owned()
        writes = [MemoryWrite(bits(32, 64), bits(0x3412, 16), 2),
                  MemoryWrite(bits(33, 64), bits(0xff, 8), 1)]
        result = apply([resource], writes)
        self.assertEqual(result.status, 'complete')
        self.assertEqual(result.writes, writes)
        self.assertEqual(result.processed_writes, 2)
        self.assertEqual(result.updates['owned'][0]['value'], bits(0x12, 8).to_dict())
        self.assertEqual(result.updates['owned'][1]['value'], bits(0xff, 8).to_dict())
        self.assertEqual(result.updates['owned'][1]['write_index'], 1)
        self.assertIn('offset_justification', result.updates['owned'][1])

    def test_uninitialized_ownership_does_not_infer_initial_bytes(self):
        resource = owned(array=None)
        result = apply([resource], [MemoryWrite(bits(33, 64), bits(0x07, 8), 1)])
        self.assertEqual(result.status, 'complete')
        self.assertIsNone(result.resources[0].byte_array)
        self.assertEqual(set(result.updates['owned']), {1})
        self.assertEqual(result.to_dict()['resources'][0]['component'], resource.component)

    def test_unknown_owner_stops_and_retains_unprocessed_stores(self):
        writes = [MemoryWrite(input_expr('unrelated'), bits(0, 8), 1),
                  MemoryWrite(bits(32, 64), bits(1, 8), 1)]
        result = apply([owned()], writes)
        self.assertEqual(result.status, 'stopped')
        self.assertEqual(result.reports[0]['kind'], 'unknown_write_owner')
        self.assertEqual(result.processed_writes, 0)
        self.assertEqual(result.writes, writes)
        self.assertFalse(result.updates['owned'])

    def test_unknown_bound_stops_without_dropping_earlier_store(self):
        resource = owned(length=1)
        writes = [MemoryWrite(bits(32, 64), bits(1, 8), 1), MemoryWrite(bits(33, 64), bits(2, 8), 1)]
        result = apply([resource], writes)
        self.assertEqual(result.status, 'stopped')
        self.assertEqual(result.processed_writes, 1)
        self.assertEqual(result.reports[0]['kind'], 'unknown_write_bounds')
        self.assertEqual(result.updates['owned'][0]['value'], bits(1, 8).to_dict())
        self.assertEqual(result.writes, writes)

    def test_unknown_alias_stops_even_with_one_matching_region(self):
        first = owned()
        second = owned('other', input_expr('other_base'))
        result = apply([first, second], [MemoryWrite(bits(32, 64), bits(1, 8), 1)])
        self.assertEqual(result.reports[0]['kind'], 'ambiguous_write_alias')

    def test_source_disjointness_fact_can_resolve_unknown_alias(self):
        first, second = owned(), owned('other', input_expr('other_base'))
        facts = [fact('disjoint_ranges', left='owned', right='other')]
        result = apply([first, second], [MemoryWrite(bits(32, 64), bits(1, 8), 1)], facts=facts)
        self.assertEqual(result.status, 'complete')
        self.assertFalse(result.updates['other'])

    def test_numeric_range_membership_never_creates_ownership(self):
        address = input_expr('address')
        conditions = [operation('bvule', bits(32, 64), address), operation('bvult', address, bits(64, 64))]
        result = apply([], [MemoryWrite(address, bits(1, 8), 1)], conditions=conditions)
        self.assertEqual(result.reports[0]['kind'], 'unknown_write_owner')

    def test_path_equality_establishes_a_relative_offset(self):
        base, address = input_expr('base'), input_expr('address')
        equality = operation('=', address, operation('bvadd', base, bits(2, 64)))
        resource = owned(base=base)
        result = apply([resource], [MemoryWrite(address, bits(1, 8), 1)], conditions=[equality])
        self.assertEqual(result.status, 'complete')
        self.assertEqual(set(result.updates['owned']), {2})
        self.assertTrue(result.updates['owned'][2]['offset_justification']['conditions'])

    def test_path_bound_can_establish_length_without_replacing_the_source(self):
        length = input_expr('length')
        condition = operation('bvuge', length, bits(4, 64))
        resource = owned(length=length)
        result = apply([resource], [MemoryWrite(bits(35, 64), bits(1, 8), 1)], conditions=[condition])
        self.assertEqual(result.status, 'complete')
        self.assertEqual(result.resources[0].length, length)
        self.assertEqual(result.updates['owned'][3]['bound_justification']['kind'], 'path_condition')

    def test_source_offset_and_length_facts_require_provenance(self):
        address, base = input_expr('address'), input_expr('base')
        resource = owned(base=base, length=input_expr('length', None))
        facts = [fact('address_equality', address=address, base=base, index=1),
                 fact('bounds', resource_id='owned', index=1, count=1)]
        result = apply([resource], [MemoryWrite(address, bits(1, 8), 1)], facts=facts)
        self.assertEqual(result.status, 'complete')
        with self.assertRaisesRegex(ValueError, 'source provenance'):
            apply([resource], [], facts=[{'kind': 'disjoint'}])

    def test_fraction_permission_is_never_guessed(self):
        for writable, reason in [(None, 'unknown_write_permission'), (False, 'write_permission_denied')]:
            with self.subTest(writable=writable):
                result = apply([owned(writable=writable)], [MemoryWrite(bits(32, 64), bits(1, 8), 1)])
                self.assertEqual(result.reports[0]['kind'], reason)
                self.assertEqual(result.reports[0]['fraction'], '(DfracOwn (1%Qp))')

    def test_little_endian_uses_the_pinned_state_convention(self):
        with self.assertRaisesRegex(ValueError, 'pinned little-endian'):
            apply([owned()], [], endianness='big')

    def test_store_value_may_contain_an_unconstrained_store_result(self):
        unknown = Expr('write_result', value='prior_store')
        value = operation('ite', unknown, bits(1, 8), bits(2, 8))
        result = apply([owned()], [MemoryWrite(bits(32, 64), value, 1)])
        self.assertEqual(result.status, 'complete')
        self.assertEqual(result.updates['owned'][0]['value'], value.to_dict())

    def test_full_fraction_flag_without_a_source_permission_fact_stops(self):
        result = apply_owned_writes([owned()], [MemoryWrite(bits(32, 64), bits(1, 8), 1)])
        self.assertEqual(result.reports[0]['kind'], 'unknown_write_permission')

    def test_symbolic_base_needs_a_nonwrap_fact(self):
        resource = owned(base=input_expr('base'))
        permission = fact('permission', resource_id=resource.id, fraction=resource.fraction)
        result = apply_owned_writes([resource], [MemoryWrite(resource.base, bits(1, 8), 1)], facts=[permission])
        self.assertEqual(result.reports[0]['kind'], 'unknown_write_nonwrap')

    def test_partial_prefix_does_not_render_as_whole_block_success(self):
        resource = owned(length=1)
        writes = [MemoryWrite(bits(32, 64), bits(1, 8), 1), MemoryWrite(bits(33, 64), bits(2, 8), 1)]
        result = apply([resource], writes)
        output = render_resource_boundary({'components': [], 'existential_prefixes': []},
                                          result, SymbolicState(), vocabulary=VOCABULARY)
        self.assertEqual(output['block_status'], 'stopped')
        self.assertEqual(output['components'], [])
        self.assertEqual(output['write_accounting']['processed_prefix']['write_count'], 1)
        self.assertIsNotNone(output['write_accounting']['blocked_event'])

    def test_array_rendering_uses_ordered_splices_and_z_endian_counts(self):
        ownership = parse_source_ownership('address ↦ₘ∗ old_bytes', provenance=PROVENANCE)
        component, = ownership['components']
        resource = OwnedBytes(component['id'], bits(32, 64), 'address', input_expr('old_bytes', None),
                              8, True, '(DfracOwn (1%Qp))', component, PROVENANCE, 8)
        result = apply([resource], [MemoryWrite(bits(32, 64), bits(0x1234, 16), 2)])
        output = render_resource_boundary(ownership, result, SymbolicState(), vocabulary=VOCABULARY)
        self.assertEqual(output['block_status'], 'completed')
        source = output['components'][0]['source']
        self.assertIn('bv_to_little_endian (Z.of_nat 2%nat) 8%N', source)
        self.assertIn('take 0%nat old_bytes', source)
        self.assertIn('drop (Nat.add 0%nat 2%nat) old_bytes', source)

    def test_uninitialized_rendering_keeps_unknown_prefix_and_suffix(self):
        ownership = parse_source_ownership('address ↦ₘ? 4%Z', provenance=PROVENANCE)
        component, = ownership['components']
        resource = OwnedBytes(component['id'], bits(32, 64), 'address', None,
                              4, True, '(DfracOwn (1%Qp))', component, PROVENANCE, 8)
        result = apply([resource], [MemoryWrite(bits(33, 64), bits(9, 8), 1)])
        output = render_resource_boundary(ownership, result, SymbolicState(), vocabulary=VOCABULARY)
        self.assertEqual(output['block_status'], 'completed')
        source = output['components'][0]['source']
        self.assertIn('↦ₘ{(DfracOwn (1%Qp))}? 1%Z', source)
        self.assertIn('(Z.add (address) 2%Z) ↦ₘ{(DfracOwn (1%Qp))}? 2%Z', source)
        self.assertIn('(BV 8%N 9%Z)', source)

    def test_missing_projected_owned_register_stops_instead_of_disappearing(self):
        ownership = parse_source_ownership('"x1" ↦ᵣ RVal_Bits before', provenance=PROVENANCE)
        result = apply([], [])
        output = render_resource_boundary(ownership, result, SymbolicState(), vocabulary=VOCABULARY)
        self.assertEqual(output['block_status'], 'stopped')
        self.assertIn('no retained final value', output['reports'][0]['detail'])
        output = render_resource_boundary(ownership, result, SymbolicState(),
                                          retained_registers={'x1': bits(7, 64)}, vocabulary=VOCABULARY)
        self.assertEqual(output['block_status'], 'completed')
        self.assertIn('(BV 64%N 7%Z)', output['components'][0]['source'])

    def test_assertion_tree_keeps_caller_outside_the_existential(self):
        witness = Expr('unknown_input', width=64, value='entry.witness')
        tree = {'kind': 'sep', 'left': {'kind': 'exists',
                'binders': [{'name': 'witness', 'type': 'bv 64', 'expression': witness.to_dict()}],
                'components': [{'id': 'owned_register', 'kind': 'register', 'register': 'x1', 'value_coq': 'witness'}]},
                'right': {'id': 'caller', 'kind': 'opaque_caller_continuation', 'coq': 'instr_pre return_address postcondition'}}
        ownership = ownership_from_assertion_tree(tree, provenance=PROVENANCE)
        output = render_resource_boundary(ownership, apply([], []), SymbolicState(registers={'x1': witness}),
                                          vocabulary=VOCABULARY)
        self.assertEqual(output['block_status'], 'completed')
        self.assertEqual(output['tree']['right'], {'kind': 'component', 'id': 'caller'})
        self.assertIn('RVal_Bits (witness : bv 64%N)', output['body'])
        self.assertTrue(output['body'].endswith(' ∗ instr_pre return_address postcondition)'))

    def test_symbolic_store_result_and_event_binding_remain_in_the_write_log(self):
        source = '(trace (declare-const ok Bool) (write-mem ok |Write_plain| #x0000000000000020 #x01 1))'
        trace, = evaluate_trace(source, SymbolicState(), instruction_index=3)
        write, = trace.state.writes
        self.assertEqual(write.result.op, 'write_result')
        self.assertEqual(write.provenance['trace_sha256'], hashlib.sha256(source.encode()).hexdigest())
        result = apply([owned()], [write])
        self.assertEqual(result.to_dict()['writes'][0]['result']['op'], 'write_result')
        self.assertEqual(result.to_dict()['writes'][0]['event_id'], write.event_id)

    def test_source_owned_uninitialized_span_maps_stores_without_initial_values(self):
        span = MemoryRegion(bits(32, 64), length=2, uninitialized=True)
        source = '''(trace (declare-const before (_ BitVec 8))
          (read-mem before |Read_plain| #x0000000000000020 1)
          (write-reg |before| nil before) (declare-const ok Bool)
          (write-mem ok |Write_plain| #x0000000000000020 #x07 1)
          (declare-const after (_ BitVec 8)) (read-mem after |Read_plain| #x0000000000000020 1)
          (write-reg |after| nil after))'''
        result, = evaluate_trace(source, SymbolicState(memory=[span]))
        self.assertEqual(result.state.registers['before'].op, 'unknown_read')
        self.assertEqual(result.state.registers['after'], bits(7, 8))
        self.assertTrue(result.state.writes[0].mapped)
        self.assertFalse(span.bytes)

    def test_vocabulary_loader_checks_sources_without_reading_capture_attachments(self):
        with tempfile.TemporaryDirectory() as directory:
            source, packet = Path(directory)/'source.v', Path(directory)/'packet.json'
            source.write_text('Definition source_rule := original.\n')
            row = {'kind': 'owned_byte_array', 'source_bindings': [{'path': str(source),
                   'sha256': hashlib.sha256(source.read_bytes()).hexdigest()}],
                   'capture_membership': '/missing/capture.json'}
            packet.write_text(json.dumps({'rows': [row], 'source_vocabulary': {'imports': []}}))
            digest = hashlib.sha256(packet.read_bytes()).hexdigest()
            result = load_resource_vocabulary(packet, digest)
            self.assertNotIn('capture_membership', result['rows'][0])
            source.write_text('changed')
            with self.assertRaisesRegex(ValueError, 'helper source changed'):
                load_resource_vocabulary(packet, digest)


if __name__ == '__main__':
    unittest.main()
