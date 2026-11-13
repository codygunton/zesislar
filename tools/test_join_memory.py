"""Whole-array reconstruction preserves every source edge and fraction."""
from copy import deepcopy
from dataclasses import replace
import json
from pathlib import Path
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parent / 'block'))
from forward_resources import OwnedBytes
from join_memory import affine_memory_image
from symbolic_state import Expr, MemoryWrite, bits, input_expr, operation


class MemoryJoinTests(unittest.TestCase):
    def fixture(self):
        data = json.loads((Path(__file__).parent / 'block/testdata/join-698c-affine.json').read_text())
        resource = OwnedBytes('output', input_expr('base'), 'base', input_expr('before', None), 40, True,
                              'DfracOwn 1', {'source': 'base ↦ₘ∗ before'}, {'source': 'fixture'}, 8)
        paths = []
        for edge in data['edges']:
            values = [(32, 2, bits(0, 16)), (0, 8, Expr.from_dict(edge['field0'])),
                      (8, 8, Expr.from_dict(edge['field8']))]
            paths.append([(MemoryWrite(operation('bvadd', resource.base, bits(offset, 64)), value, size, True,
                                        ownership_id='output', provenance={'source': 'fixture'}), offset)
                          for offset, size, value in values])
        basis = {name: [Expr.from_dict(edge['basis'][name]) for edge in data['edges']]
                 for name in data['edges'][0]['basis']}
        expressions = {'x11': input_expr('machine_x11'), 'x12': input_expr('machine_x12'),
                       'input': Expr.from_dict(data['edges'][0]['basis']['input'])}
        return resource, paths, basis, expressions

    def image(self, resource, paths, basis, expressions):
        return affine_memory_image(resource, paths, basis=basis, expressions=expressions,
                                    register_names=['x11', 'x12'], vocabulary={})

    def test_nine_edges_reconstruct_one_whole_fractional_array(self):
        resource, paths, basis, expressions = self.fixture()
        result = self.image(resource, paths, basis, expressions)
        self.assertEqual(result['status'], 'generated')
        self.assertEqual(result['edge_count'], 9)
        self.assertEqual(len(result['relations']), 2)
        self.assertIn('↦ₘ{DfracOwn 1}∗', result['source'])
        self.assertIn('machine_x11', result['value'])
        self.assertIn('machine_x12', result['value'])
        self.assertFalse(result['proof_established'])

    def test_different_write_layout_refuses(self):
        resource, paths, basis, expressions = self.fixture()
        paths[-1] = paths[-1][:-1]
        self.assertEqual(self.image(resource, paths, basis, expressions)['status'], 'refused')

    def test_unknown_original_array_requires_packaging(self):
        resource, paths, basis, expressions = self.fixture()
        self.assertEqual(self.image(replace(resource, byte_array=None), paths, basis, expressions)['status'], 'refused')

    def test_an_unowned_store_refuses(self):
        resource, paths, basis, expressions = self.fixture()
        write, offset = paths[0][0]
        paths[0][0] = replace(write, ownership_id='other'), offset
        with self.assertRaisesRegex(ValueError, 'typed source owner'):
            self.image(resource, paths, basis, expressions)

    def test_edges_without_stores_leave_the_array_to_packaging(self):
        # The edges state the array differently only through their seeds; no store layout rebuilds that.
        resource, _, basis, expressions = self.fixture()
        result = self.image(resource, [[] for _ in range(9)], basis, expressions)
        self.assertEqual((result['status'], result['detail']), ('refused', 'The array needs explicit packaging'))

    def test_a_symbolic_offset_store_leaves_the_array_to_packaging(self):
        resource, paths, basis, expressions = self.fixture()
        write, _ = paths[0][0]
        paths[0][0] = write, operation('bvsub', write.address, resource.base)
        result = self.image(resource, paths, basis, expressions)
        self.assertEqual((result['status'], result['detail']), ('refused', 'A store has a symbolic offset'))

    def test_source_paths_remain_unchanged(self):
        resource, paths, basis, expressions = self.fixture()
        before = deepcopy(paths)
        self.image(resource, paths, basis, expressions)
        self.assertEqual(paths, before)


if __name__ == '__main__':
    unittest.main()
