"""Ownership checks stop CFG propagation before another instruction executes."""
from pathlib import Path
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parent / 'block'))
from forward_resource_design import _state_from_result, evaluate_owned_function
from forward_resources import OwnedBytes, parse_source_ownership
from resource_seed import OwnedSeed
from symbolic_state import Expr, MemoryRegion, SymbolicState, bits, input_expr, operation


PROVENANCE = {'source': 'public.v', 'definition': 'entry'}
VOCABULARY = {'input_sha256': 'fixture', 'source_vocabulary': {'imports': []}}


def fact(kind, **terms):
    return {'fact_id': kind+repr(terms), 'kind': kind, 'terms': terms, 'origin': PROVENANCE, 'status': 'supplied'}


def seed():
    ownership = parse_source_ownership('"x1" ↦ᵣ RVal_Bits original ∗ base ↦ₘ∗ bytes ∗ caller', provenance=PROVENANCE)
    component = ownership['components'][1]
    resource = OwnedBytes(component['id'], bits(32, 64), 'base', input_expr('bytes', None), 4,
                          True, 'DfracOwn 1', component, PROVENANCE, 8)
    state = SymbolicState(registers={'PC': bits(16, 64), 'x1': input_expr('original')},
                          memory=[MemoryRegion(resource.base, byte_array=resource.byte_array,
                                               length=4, ownership_id=resource.id)])
    facts = [fact('permission', resource_id=resource.id, fraction=resource.fraction)]
    return OwnedSeed(state, ownership, [resource], facts, [])


def cfg(first_end=20):
    return {'name': 'example', 'entry': 16, 'end': 28,
            'rows': [{'pc': pc} for pc in range(16, 28, 4)],
            'blocks': [{'start': 16, 'end': first_end, 'successors': [first_end]},
                       {'start': first_end, 'end': 28, 'successors': []}], 'loops': []}


class ForwardResourceDesignTests(unittest.TestCase):
    def test_loop_read_metadata_survives_state_copy_and_result_decode(self):
        state = seed().state
        state.symbolic_read_ranges = [{'owner': 'array', 'first': 1, 'last': 8}]
        state.read_obligations = [{'kind': 'open_range', 'source_index': 2}]
        record = state.to_dict()
        copied = state.copy()
        restored = _state_from_result(record)
        self.assertEqual(restored.to_dict(), record)
        self.assertEqual(copied.to_dict(), record)
        copied.symbolic_read_ranges[0]['last'] = 4
        copied.read_obligations[0]['source_index'] = 3
        self.assertEqual(state.symbolic_read_ranges[0]['last'], 8)
        self.assertEqual(state.read_obligations[0]['source_index'], 2)

    def test_absent_loop_read_metadata_preserves_the_existing_result_shape(self):
        record = seed().state.to_dict()
        self.assertNotIn('symbolic_read_ranges', record)
        self.assertNotIn('read_obligations', record)
        self.assertEqual(_state_from_result(record).to_dict(), record)

    def test_source_declaration_metadata_preserves_execution_and_resources(self):
        traces = {16: '(trace (declare-const v7 (_ BitVec 64)) (write-reg |x1| nil v7) (write-reg |PC| nil #x0000000000000014))',
                  20: '(trace (write-reg |PC| nil #x0000000000000018))',
                  24: '(trace (write-reg |PC| nil #x0000000000000000))'}
        baseline = evaluate_owned_function(cfg(), traces, {16: seed()}, vocabulary=VOCABULARY)
        captured = evaluate_owned_function(cfg(), traces, {16: seed()}, vocabulary=VOCABULARY,
                                          capture_witness_origins=True)
        states = [alternative['state'] for boundary in captured['boundaries']
                  for alternative in boundary['alternatives']] + [stop['state'] for stop in captured['stops']]
        origins = [row for state in states for row in state['reports']
                   if row.get('kind') == 'source_witness_origin']
        self.assertTrue(origins)
        self.assertTrue(all(row['instruction_pc'] == '0x10' and row['declaration'] == 'v7'
                            and row['declaration_type'] == ['_', 'BitVec', '64'] for row in origins))
        def without_origins(value):
            if isinstance(value, dict):
                return {key: without_origins(child) for key, child in value.items()}
            if isinstance(value, list):
                return [without_origins(child) for child in value
                        if not isinstance(child, dict) or child.get('kind') != 'source_witness_origin']
            return value
        self.assertEqual(without_origins(captured), baseline)

    def test_dead_owned_register_keeps_its_actual_final_value(self):
        traces = {16: '(trace (write-reg |x1| nil #x0000000000000007) (write-reg |PC| nil #x0000000000000014))',
                  20: '(trace (write-reg |PC| nil #x0000000000000018))',
                  24: '(trace (write-reg |PC| nil #x0000000000000000))'}
        report = evaluate_owned_function(cfg(), traces, {16: seed()}, vocabulary=VOCABULARY)
        second = next(row for row in report['boundaries'] if row['pc'] == '0x14')['alternatives'][0]
        self.assertNotIn('x1', second['state']['registers'])
        self.assertEqual(second['state']['retained_registers']['x1'], bits(7, 64).to_dict())
        self.assertIn('(BV 64%N 7%Z)', second['resource_boundary']['components'][0]['source'])

    def test_unknown_store_owner_stops_before_the_next_instruction(self):
        source = seed()
        source.state.registers['x2'] = input_expr('unrelated')
        traces = {16: '''(trace (declare-const address (_ BitVec 64)) (read-reg |x2| nil address)
          (declare-const ok Bool) (write-mem ok |Write_plain| address #x01 1)
          (write-reg |PC| nil #x0000000000000014))''',
                  20: '(trace (forbidden-following-instruction))',
                  24: '(trace (write-reg |PC| nil #x0000000000000000))'}
        report = evaluate_owned_function(cfg(24), traces, {16: source}, vocabulary=VOCABULARY)
        stop, = report['stops']
        self.assertEqual(stop['reason'], 'state_check')
        self.assertEqual(stop['state']['trace_count'], 1)
        self.assertEqual(stop['detail']['blocked_event']['report']['kind'], 'unknown_write_owner')
        self.assertEqual(len(stop['detail']['writes']), 1)
        self.assertEqual(report['boundaries'][1]['status'], 'unreachable')

    def test_nonzero_length_view_supports_a_source_array_read(self):
        source = seed()
        resource = source.resources[0]
        source.resources[0] = OwnedBytes(resource.id, resource.base, resource.address_z, resource.byte_array,
                                         input_expr('length bytes', None), resource.writable, resource.fraction,
                                         resource.component, resource.provenance, 8)
        length = input_expr('length_word')
        source.state.memory[0] = MemoryRegion(resource.base, byte_array=resource.byte_array,
                                              length=input_expr('length bytes', None), ownership_id=resource.id)
        source.state.conditions.append(operation('not', operation('=', length, bits(0, 64))))
        source.facts.append(fact('bounds', resource_id=resource.id, length_view=length.to_dict()))
        traces = {16: '''(trace (declare-const value (_ BitVec 8)) (read-mem value |Read_plain| #x0000000000000020 1)
          (write-reg |x1| nil ((_ zero_extend 56) value)) (write-reg |PC| nil #x0000000000000014))''',
                  20: '(trace (write-reg |PC| nil #x0000000000000018))',
                  24: '(trace (write-reg |PC| nil #x0000000000000000))'}
        report = evaluate_owned_function(cfg(), traces, {16: source}, vocabulary=VOCABULARY)
        alternative = report['boundaries'][1]['alternatives'][0]
        value = alternative['state']['retained_registers']['x1']
        self.assertEqual(value['op'], 'zero_extend')
        self.assertEqual(value['args'][0]['op'], 'array_byte')
        self.assertEqual(alternative['resource_boundary']['block_status'], 'completed')

    def test_supplied_disjointness_preserves_read_after_another_owned_store(self):
        source = seed()
        resource = source.resources[0]
        other_base = input_expr('other_base')
        other = OwnedBytes('other', other_base, 'other_base_z', input_expr('other_bytes', None), 4,
                            True, 'DfracOwn 1', {'source': 'other_base_z ↦ₘ∗ other_bytes'}, PROVENANCE, 8)
        source.resources.append(other)
        source.ownership['components'].append({'id': 'other', 'kind': 'byte_array',
            'source': 'other_base_z ↦ₘ∗ other_bytes', 'provenance': PROVENANCE})
        source.state.memory.append(MemoryRegion(other.base, byte_array=other.byte_array,
                                                  length=4, ownership_id=other.id))
        source.state.registers['x2'] = other_base
        source.facts.extend([fact('permission', resource_id=other.id, fraction=other.fraction),
                             fact('nonwrap', resource_id=other.id),
                             fact('disjoint_ranges', left=resource.id, right=other.id)])
        traces = {16: '''(trace (declare-const address (_ BitVec 64)) (read-reg |x2| nil address)
          (declare-const ok Bool) (write-mem ok |Write_plain| address #x01 1)
          (write-reg |PC| nil #x0000000000000014))''',
                  20: '''(trace (declare-const value (_ BitVec 8)) (read-mem value |Read_plain| #x0000000000000020 1)
          (write-reg |x1| nil ((_ zero_extend 56) value)) (write-reg |PC| nil #x0000000000000018))''',
                  24: '(trace (write-reg |PC| nil #x0000000000000000))'}
        report = evaluate_owned_function(cfg(), traces, {16: source}, vocabulary=VOCABULARY)
        self.assertFalse(any(stop['reason'] == 'state_check' for stop in report['stops']))
        final = report['stops'][-1]['state']['retained_registers']['x1']
        self.assertEqual(final['args'][0]['op'], 'array_byte')


if __name__ == '__main__':
    unittest.main()
