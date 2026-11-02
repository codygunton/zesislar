"""Source-bound dynamic reads retain their range obligations and ownership."""
import unittest

try:
    from .symbolic_state import (Expr, MemoryRegion, MemoryWrite, SymbolicState,
                                 bits, evaluate_trace, input_expr, operation)
    from .forward_resource_design import _state_from_result
except ImportError:
    from symbolic_state import (Expr, MemoryRegion, MemoryWrite, SymbolicState,
                                bits, evaluate_trace, input_expr, operation)
    from forward_resource_design import _state_from_result


TRACE = '''(trace
 (declare-const cursor (_ BitVec 64)) (read-reg |x15| () cursor)
 (declare-const byte (_ BitVec 8)) (read-mem byte |Read_plain| cursor 1)
 (write-reg |x16| () ((_ zero_extend 56) byte)))'''


class SymbolicLoopReadTests(unittest.TestCase):
    def fixture(self):
        base, address = input_expr('input_base', 64), input_expr('cursor', 64)
        limit = input_expr('endpoint', 64)
        array = input_expr('input_bytes', None)
        state = SymbolicState(registers={'x15': address}, memory=[MemoryRegion(
            base, byte_array=array, length=input_expr('List.length input_bytes', None),
            ownership_id='source_input')])
        state.symbolic_read_ranges = [{'ownership_id': 'source_input',
            'address': address.to_dict(), 'lower': operation('bvadd', base, bits(1, 64)).to_dict(),
            'limit': limit.to_dict(), 'end': input_expr('input_end', 64).to_dict(),
            'provenance': {'source': 'synthetic_loop_invariant_control'}}]
        return state

    def test_dynamic_byte_carries_one_open_range_obligation(self):
        source = self.fixture()
        original = source.to_dict()
        result, = evaluate_trace(TRACE, source)
        self.assertEqual(source.to_dict(), original)
        byte = result.state.registers['x16'].args[0]
        self.assertEqual(byte.op, 'owned_array_byte')
        self.assertEqual(byte.args[0], source.memory[0].byte_array)
        self.assertEqual(byte.args[1], source.registers['x15'])
        self.assertEqual(byte.args[2], source.memory[0].base)
        self.assertEqual(len(result.state.read_obligations), 1)
        obligation = result.state.read_obligations[0]
        self.assertEqual(obligation['owner'], 'source_input')
        self.assertEqual(obligation['status'], 'OPEN')
        self.assertEqual(len(obligation['source_chain']), 3)
        self.assertEqual(result.state.conditions, source.conditions)
        self.assertEqual(result.state.memory, source.memory)
        self.assertIn('Z.to_nat', byte.coq())

    def test_explicit_out_of_range_refuses(self):
        source = self.fixture()
        limit = Expr.from_dict(source.symbolic_read_ranges[0]['limit'])
        source.conditions.append(operation('not', operation('bvult', source.registers['x15'], limit)))
        result, = evaluate_trace(TRACE, source)
        self.assertEqual(result.state.registers['x16'].args[0].op, 'unknown_read')
        self.assertFalse(result.state.read_obligations)
        self.assertTrue(any(row['kind'] == 'out_of_range_symbolic_read' for row in result.state.reports))

    def test_closed_offset_path_is_identical(self):
        source = self.fixture()
        source.memory[0] = MemoryRegion(source.memory[0].base,
            byte_array=source.memory[0].byte_array, length=16, ownership_id='source_input')
        source.registers['x15'] = operation('bvadd', source.memory[0].base, bits(3, 64))
        baseline = source.copy()
        baseline.symbolic_read_ranges = []
        expected, = evaluate_trace(TRACE, baseline)
        actual, = evaluate_trace(TRACE, source)
        self.assertEqual(actual.state.registers['x16'], expected.state.registers['x16'])
        self.assertEqual(actual.state.reports, expected.state.reports)
        self.assertEqual(actual.state.conditions, expected.state.conditions)
        self.assertFalse(actual.state.read_obligations)
        self.assertEqual(actual.state.registers['x16'].args[0].op, 'array_byte')
        self.assertEqual(actual.state.registers['x16'].args[0].value, 3)

    def test_missing_source_owner_refuses(self):
        source = self.fixture()
        source.symbolic_read_ranges[0]['ownership_id'] = 'another_owner'
        result, = evaluate_trace(TRACE, source)
        self.assertEqual(result.state.registers['x16'].args[0].op, 'unknown_read')
        self.assertFalse(result.state.read_obligations)

    def test_missing_window_keeps_unknown_read(self):
        source = self.fixture()
        source.symbolic_read_ranges = []
        result, = evaluate_trace(TRACE, source)
        self.assertEqual(result.state.registers['x16'].args[0].op, 'unknown_read')
        self.assertFalse(result.state.read_obligations)

    def test_same_owner_write_refuses_stale_image(self):
        source = self.fixture()
        source.writes = [MemoryWrite(source.memory[0].base, bits(0, 8), 1,
                                     mapped=True, ownership_id='source_input')]
        result, = evaluate_trace(TRACE, source)
        self.assertEqual(result.state.registers['x16'].args[0].op, 'unknown_read')
        self.assertFalse(result.state.read_obligations)

    def test_roundtrip_preserves_windows_and_obligations(self):
        source = self.fixture()
        result, = evaluate_trace(TRACE, source)
        restored = _state_from_result(result.state.to_dict())
        self.assertEqual(restored.to_dict(), result.state.to_dict())
        self.assertEqual(restored.copy().to_dict(), restored.to_dict())


if __name__ == '__main__':
    unittest.main()
