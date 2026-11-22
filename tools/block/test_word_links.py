"""Word links: a load of an owned cell that the contract links to a quantity reads that quantity."""
from pathlib import Path
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parent))
from resource_seed import source_z_expression
from symbolic_state import Expr, MemoryRegion, MemoryWrite, SymbolicState, _Evaluator, bits, input_expr, operation


def base(term):
    return source_z_expression(term, {})


CELL, INTERP, DATA = base('tContextPointer args'), base('tInterpreterPointer args'), base('tStackDataPointer args')


def plus(address, offset):
    return operation('bvadd', address, bits(offset, 64))


def state(links=True):
    regions = [MemoryRegion(CELL, byte_array=input_expr('tContextCell args', None), length=8, ownership_id='cell'),
               MemoryRegion(INTERP, byte_array=input_expr('tInterpreter args', None), length=688, ownership_id='interp'),
               MemoryRegion(DATA, byte_array=input_expr('tStackData args', None), length=64, ownership_id='data')]
    result = SymbolicState(memory=regions,
                           memory_disjoint=[('cell', 'interp'), ('cell', 'data'), ('interp', 'data')])
    if links:
        result.word_links = [
            {'array': regions[0].byte_array, 'offset': 0, 'size': 8, 'value': INTERP,
             'fact_id': 'wellformed:word-link-7', 'resource_id': 'cell'},
            {'array': regions[1].byte_array, 'offset': 0x238, 'size': 8, 'value': DATA,
             'fact_id': 'wellformed:word-link-8', 'resource_id': 'interp'},
            {'array': regions[1].byte_array, 'offset': 0x248, 'size': 8, 'value': base('tStackLength args'),
             'fact_id': 'wellformed:word-link-9', 'resource_id': 'interp'}]
    return result


def store(evaluator, address, size, owner=None):
    evaluator.state.writes.append(MemoryWrite(address, bits(7, 8 * size), size, True, ownership_id=owner))


def unknown(expr):
    return expr.op == 'unknown_read' or any(unknown(arg) for arg in expr.args)


def leaves(expr):
    yield expr
    for arg in expr.args:
        yield from leaves(arg)


class WordLinks(unittest.TestCase):
    def test_a_load_of_a_linked_cell_reads_the_linked_pointer(self):
        evaluator = _Evaluator(state())
        self.assertEqual(evaluator.memory_read(CELL, 8), INTERP)
        report, = [row for row in evaluator.state.reports if row['kind'] == 'word_link_read']
        self.assertEqual((report['fact_id'], report['owner']), ('wellformed:word-link-7', 'cell'))

    def test_a_two_step_chain_reaches_the_second_array(self):
        evaluator = _Evaluator(state())
        interpreter = evaluator.memory_read(CELL, 8)
        data = evaluator.memory_read(plus(interpreter, 0x238), 8)
        self.assertEqual(data, DATA)
        word = evaluator.memory_read(plus(data, 8), 8)
        self.assertFalse(unknown(word))
        self.assertIn(Expr('array_byte', (input_expr('tStackData args', None),), 8, 8), list(leaves(word)))
        self.assertEqual(evaluator.memory_read(plus(interpreter, 0x248), 8), base('tStackLength args'))
        self.assertNotIn('ambiguous_memory_alias', [row['kind'] for row in evaluator.state.reports])

    def test_without_links_the_load_is_the_bytes_and_the_next_access_is_unknown(self):
        evaluator = _Evaluator(state(links=False))
        word = evaluator.memory_read(CELL, 8)
        self.assertEqual(word.op, 'concat')
        self.assertTrue(unknown(evaluator.memory_read(plus(word, 0x238), 8)))
        self.assertIn('ambiguous_memory_alias', [row['kind'] for row in evaluator.state.reports])
        self.assertNotIn('word_links', state(links=False).to_dict())

    def test_an_overlapping_store_drops_the_link(self):
        evaluator = _Evaluator(state())
        store(evaluator, plus(INTERP, 0x23c), 4, 'interp')
        word = evaluator.memory_read(plus(INTERP, 0x238), 8)
        self.assertNotEqual(word, DATA)
        self.assertFalse(unknown(word))    # the stored bytes and the remaining array bytes

    def test_a_disjoint_store_keeps_the_link(self):
        evaluator = _Evaluator(state())
        store(evaluator, plus(INTERP, 0x240), 8, 'interp')
        store(evaluator, plus(DATA, 0), 8, 'data')
        self.assertEqual(evaluator.memory_read(plus(INTERP, 0x238), 8), DATA)

    def test_a_store_through_an_unknown_pointer_drops_the_link(self):
        evaluator = _Evaluator(state())
        store(evaluator, input_expr('somewhere', 64), 8)
        self.assertTrue(unknown(evaluator.memory_read(CELL, 8)))

    def test_a_partial_or_shifted_read_is_not_linked(self):
        evaluator = _Evaluator(state())
        self.assertEqual(evaluator.memory_read(plus(INTERP, 0x239), 8).op, 'concat')
        self.assertEqual(evaluator.memory_read(plus(INTERP, 0x238), 4).op, 'concat')

    def test_links_survive_copy_and_the_result_round_trip(self):
        from forward_resource_design import _state_from_result
        original = state()
        self.assertEqual(original.copy().word_links, original.word_links)
        self.assertEqual(_state_from_result(original.to_dict()).word_links, original.word_links)

    def test_a_hexadecimal_offset_in_an_address_is_a_constant(self):
        self.assertEqual(base('bv_unsigned (tHost args) + 0x98'),
                         operation('bvadd', input_expr('tHost args', 64), bits(0x98, 64)))


if __name__ == '__main__':
    unittest.main()
