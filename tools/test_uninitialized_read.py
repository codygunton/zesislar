"""A load from owned uninitialized bytes reads fresh existential bytes with no facts."""
from pathlib import Path
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parent / 'block'))
from forward_resources import apply_owned_writes, ownership_from_assertion_tree, render_resource_boundary
from symbolic_state import MemoryRegion, SymbolicState, bits, evaluate_trace, uninitialized_binder

LOAD = '''(trace (declare-const value (_ BitVec 64))
  (read-mem value |Read_plain| #x0000000000000020 8) (write-reg |x10| nil value))'''
STORE_THEN_LOAD = '''(trace (declare-const ok Bool) (write-mem ok |Write_plain| #x0000000000000020 #x07 1)
  (declare-const value (_ BitVec 16)) (read-mem value |Read_plain| #x0000000000000020 2) (write-reg |x10| nil value))'''


def span(length=16, owner='resource_11'):
    return MemoryRegion(bits(32, 64), length=length, uninitialized=True, ownership_id=owner)


def load(source, region):
    result, = evaluate_trace(source, SymbolicState(memory=[region]))
    return result


class UninitializedRead(unittest.TestCase):
    def test_an_owned_uninitialized_load_reads_fresh_bytes_without_facts(self):
        result = load(LOAD, span())
        value = result.state.registers['x10']
        reads = value.uninitialized_reads()
        self.assertEqual(len(reads), 8)
        self.assertEqual(len({uninitialized_binder(read)['name'] for read in reads}), 8)
        self.assertNotIn('unknown_read', str(value.to_dict()))
        self.assertEqual(result.state.conditions, [])
        rows = [row for row in result.state.reports if row['kind'] == 'uninitialized_read']
        self.assertEqual([row['owner'] for row in rows], ['resource_11'] * 8)
        self.assertIn('uninit_byte_', value.coq())

    def test_a_written_byte_keeps_its_value_and_the_next_byte_is_fresh(self):
        value = load(STORE_THEN_LOAD, span()).state.registers['x10']
        self.assertEqual(len(value.uninitialized_reads()), 1)
        self.assertIn('(BV 8%N 7%Z)', value.coq())

    def test_unowned_or_out_of_extent_bytes_stay_unknown(self):
        self.assertEqual(load(LOAD, span(owner=None)).state.registers['x10'].uninitialized_reads(), [])
        self.assertIn('unknown_read', str(load(LOAD, span(length=4)).state.registers['x10'].to_dict()))

    def test_the_boundary_binds_each_fresh_byte(self):
        value = load(LOAD, span()).state.registers['x10']
        tree = {'kind': 'sep', 'left': {'kind': 'exists', 'binders': [],
                'components': [{'id': 'owned_register', 'kind': 'register', 'register': 'x10', 'value_coq': 'v'}]},
                'right': {'id': 'caller', 'kind': 'opaque_caller_continuation', 'coq': 'instr_pre r q'}}
        ownership = ownership_from_assertion_tree(tree, provenance={'source': 'entry.v'})
        output = render_resource_boundary(ownership, apply_owned_writes([], []), SymbolicState(registers={'x10': value}),
                                          vocabulary={'input_sha256': 'fixture',
                                                      'source_vocabulary': {'imports': []}})
        self.assertEqual(output['block_status'], 'completed')
        names = [binder['name'] for binder in output['fresh_binders']]
        self.assertEqual(names, [uninitialized_binder(read)['name'] for read in value.uninitialized_reads()])
        self.assertTrue(all(binder['type'] == 'bv 8' for binder in output['fresh_binders']))
        self.assertTrue(all(name in output['body'] for name in names))


if __name__ == '__main__':
    unittest.main()
