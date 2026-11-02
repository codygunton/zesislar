from copy import deepcopy
import unittest
from pathlib import Path
import sys
sys.path.insert(0, str(Path(__file__).resolve().parent / "block"))
from typed_seed_adapter import adapt
from forward_resources import ownership_from_assertion_tree, _render_tree


def seed():
    return {'BODY': 'protected original body', 'parameters': [{'name': 'p', 'type': 'bv 64%N'}],
            'assertion_tree': {'kind': 'exists', 'binders': [{'name': 'xs', 'type': 'list (bv 8%N)'}],
                'components': [{'kind': 'typed_array', 'id': 'owner', 'coq': 'base ↦ₘ{DfracOwn 1}∗ (xs : list (bv 8%N))',
                                'fraction': 'DfracOwn 1', 'byte_size': 7, 'uninitialized': True},
                               {'kind': 'pure', 'id': 'length', 'coq': 'List.length xs = 7%nat'}]}}


class TypedAdapterTests(unittest.TestCase):
    def test_preserves_all_source_assertions_and_order(self):
        original = seed(); saved = deepcopy(original); result, changes = adapt(original)
        self.assertEqual(original, saved)
        self.assertEqual(result['BODY'], original['BODY'])
        self.assertEqual(result['parameters'], original['parameters'])
        self.assertEqual(result['assertion_tree']['binders'], original['assertion_tree']['binders'])
        self.assertEqual(result['assertion_tree']['components'][1], original['assertion_tree']['components'][1])
        owner = result['assertion_tree']['components'][0]
        self.assertEqual(owner['original_component'], original['assertion_tree']['components'][0]['coq'])
        self.assertEqual(owner['byte_array_expr'], {'op': 'input', 'value': 'xs'})
        self.assertTrue(owner['uninitialized'])
        self.assertEqual(owner['fraction'], 'DfracOwn 1')
        self.assertEqual(len(changes), 1)

    def test_rendered_assertions_and_scopes_remain_exact(self):
        original = seed(); result, _ = adapt(original)
        before = ownership_from_assertion_tree(original['assertion_tree'], provenance={})
        after = ownership_from_assertion_tree(result['assertion_tree'], provenance={})
        for left, right in zip(before['components'], after['components']):
            self.assertEqual(left['source'], right['source'])
            self.assertEqual(left['scope'], right['scope'])
            self.assertEqual(left.get('fraction'), right.get('fraction'))
        def body(view):
            return _render_tree(view['tree'], {row['id']: row['source'] for row in view['components']})
        self.assertEqual(body(before), body(after))

    def test_refuses_missing_or_wrong_binder_type(self):
        for type_ in ['list (bv 16%N)', 'Z']:
            value = seed(); value['assertion_tree']['binders'][0]['type'] = type_
            with self.assertRaises(ValueError): adapt(value)

    def test_refuses_fraction_mismatch(self):
        value = seed(); value['assertion_tree']['components'][0]['fraction'] = 'DfracOwn (1/2)'
        with self.assertRaises(ValueError): adapt(value)

    def test_refuses_hidden_expression(self):
        value = seed(); value['assertion_tree']['components'][0]['coq'] = 'base ↦ₘ{DfracOwn 1}∗ (f xs : list (bv 8%N))'
        with self.assertRaises(ValueError): adapt(value)

    def test_refuses_conflicting_view(self):
        value = seed(); value['assertion_tree']['components'][0]['element_bits'] = 16
        with self.assertRaises(ValueError): adapt(value)

    def test_refuses_shadowed_scope(self):
        value = seed(); value['assertion_tree']['components'].append(deepcopy(value['assertion_tree']))
        with self.assertRaises(ValueError): adapt(value)


if __name__ == '__main__': unittest.main()
