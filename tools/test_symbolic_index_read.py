"""Read an owned array at a symbolic index as a list lookup with an index range."""
from pathlib import Path
import sys
import unittest

sys.path.insert(0, str(Path(__file__).parent / 'block'))
from symbolic_state import Expr, MemoryRegion, SymbolicState, _Evaluator, bits, input_expr, operation


def evaluator(*regions, writes=(), disjoint=()):
    state = SymbolicState(registers={'PC': bits(0, 64)}, memory=list(regions), writes=list(writes),
                          memory_disjoint=list(disjoint))
    return _Evaluator(state)


LISTS = MemoryRegion(bits(0x1000, 64), (), input_expr('lists', None), 184, ownership_id='resource_10')
INDEX = operation('bvshl', input_expr('i'), bits(3, 64))


class SymbolicIndexRead(unittest.TestCase):
    def test_constant_base_with_symbolic_index_reads_the_owned_array(self):
        machine = evaluator(LISTS)
        address = operation('bvadd', operation('bvadd', bits(0x1000, 64), INDEX), bits(8, 64))
        value = machine.memory_byte(address)
        self.assertEqual(value.op, 'owned_array_byte')
        self.assertEqual(value.args, (LISTS.byte_array, address, LISTS.base))
        index = operation('bvsub', address, LISTS.base)
        self.assertIn(operation('bvult', index, bits(184, 64)), machine.state.conditions)
        row, = machine.state.read_obligations
        self.assertEqual((row['kind'], row['status'], row['owner']),
                         ('owned_symbolic_byte_range', 'OPEN', 'resource_10'))
        self.assertEqual(row['value'], value.to_dict())

    def test_symbolic_base_must_be_an_addend(self):
        buffer = MemoryRegion(input_expr('buffer'), (), input_expr('bytes', None), 64, ownership_id='resource_9')
        machine = evaluator(buffer)
        self.assertEqual(machine.memory_byte(operation('bvadd', input_expr('buffer'), INDEX)).op, 'owned_array_byte')
        self.assertEqual(evaluator(buffer).memory_byte(operation('bvadd', input_expr('other'), INDEX)).op,
                         'unknown_read')

    def test_out_of_extent_constant_and_uninitialized_regions_stay_unknown(self):
        far = operation('bvadd', operation('bvadd', bits(0x1000, 64), INDEX), bits(200, 64))
        self.assertEqual(evaluator(LISTS).memory_byte(far).op, 'unknown_read')
        stack = MemoryRegion(bits(0x1000, 64), (), None, 16, uninitialized=True, ownership_id='resource_11')
        self.assertEqual(evaluator(stack).memory_byte(
            operation('bvadd', bits(0x1000, 64), INDEX)).op, 'unknown_read')

    def test_two_matching_arrays_are_ambiguous(self):
        other = MemoryRegion(bits(0x1000, 64), (), input_expr('copy', None), 184, ownership_id='resource_12')
        address = operation('bvadd', bits(0x1000, 64), INDEX)
        self.assertEqual(evaluator(LISTS, other).memory_byte(address).op, 'unknown_read')

    def test_a_list_length_array_states_its_actual_length_not_its_minimum(self):
        # The seed knows only that the length is at least 1; a later element is beyond 1.
        length = input_expr('List.length (input args)', None)
        array = MemoryRegion(input_expr('input_base'), (), input_expr('input args', None), length,
                             ownership_id='resource_7', minimum_length=1)
        machine = evaluator(array)
        address = operation('bvadd', input_expr('input_base'), input_expr('cursor'))
        self.assertEqual(machine.memory_byte(address).op, 'owned_array_byte')
        bound = input_expr('(Z_to_bv 64%N (Z.of_nat (List.length (input args))))', 64)
        self.assertEqual(machine.state.conditions,
                         [operation('bvult', operation('bvsub', address, input_expr('input_base')), bound)])

    def test_an_array_without_a_length_term_stops_the_read(self):
        array = MemoryRegion(input_expr('input_base'), (), input_expr('input args', None),
                             input_expr('opaque_extent', None), ownership_id='resource_7', minimum_length=1)
        machine = evaluator(array)
        address = operation('bvadd', input_expr('input_base'), input_expr('cursor'))
        self.assertEqual(machine.memory_byte(address).op, 'unknown_read')
        self.assertEqual(machine.state.conditions, [])


if __name__ == '__main__':
    unittest.main()
