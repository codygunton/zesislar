"""Keep source views scoped consistently across incoming guards and resources."""
from copy import deepcopy
from pathlib import Path
import sys
import unittest

sys.path.insert(0, str(Path(__file__).parent / 'block'))
from loop_join_resources import guard_incoming_boundary
from symbolic_state import input_expr, bits, operation, Expr


class IncomingGuards(unittest.TestCase):
    def fixture(self):
        word = input_expr('sourceWord')
        owner = 'reg_col sourceRegisters'
        resource = '(32)%Z ↦ₘ{DfracOwn 1}∗ bytes'
        condition = operation('=', word, bits(0, 64)).to_dict()
        boundary = {'block_status': 'completed', 'path_conditions': [condition],
            'tree': {'kind': 'exists', 'binders': [{'name': 'word', 'type': 'bv 64'}],
                     'body': {'kind': 'sep_list', 'children': [
                         {'kind': 'component', 'id': 'owner'}, {'kind': 'component', 'id': 'memory'}]}},
            'components': [{'id': 'owner', 'source': owner, 'provenance': {'source': 'owned'}},
                           {'id': 'memory', 'source': resource, 'provenance': {'source': 'owned'}}]}
        view = {'name': 'sourceWord', 'type': 'bv 64', 'expression': word.to_dict(),
                'source_view': {'owner_id': 'owner', 'owner_source': owner,
                    'source_expression': word.to_dict(), 'checked_application': 'bound helper result'}}
        return boundary, view

    def render(self, boundary, view):
        return guard_incoming_boundary(boundary, source_words=[view], provenance={'source': 'bound-path'})

    def test_source_word_is_bound_before_its_guard_and_resources_remain_exact(self):
        boundary, view = self.fixture();before = deepcopy(boundary)
        result = self.render(boundary, view)
        self.assertEqual(result['status'], 'rendered')
        self.assertIn('(sourceWord : bv 64)', result['boundary']['body'])
        self.assertIn('bool_decide (sourceWord =', result['boundary']['body'])
        self.assertEqual(result['boundary']['components'][:2], boundary['components'])
        self.assertIn('↦ₘ{DfracOwn 1}∗ bytes', result['boundary']['body'])
        self.assertEqual(result['source_words'], [view])
        self.assertEqual(boundary, before)

    def test_wrong_owner_expression_type_and_capture_refuse(self):
        for defect in ['owner', 'source', 'expression', 'type', 'capture', 'renamed_alias']:
            with self.subTest(defect=defect):
                boundary, view = self.fixture()
                if defect == 'owner':view['source_view']['owner_id'] = 'missing'
                elif defect == 'source':view['source_view']['owner_source'] = 'reg_col anotherCollection'
                elif defect == 'expression':view['source_view']['source_expression'] = input_expr('anotherWord').to_dict()
                elif defect == 'type':view['type'] = 'bv 32'
                elif defect == 'capture':view['name'] = 'word'
                else:view['name'] = 'unrelatedWord'
                with self.assertRaises(ValueError):self.render(boundary, view)

    def test_each_path_keeps_its_own_scope(self):
        boundary, view = self.fixture()
        first = self.render(boundary, view);second = self.render(boundary, view)
        first['boundary']['tree']['binders'].append({'name': 'onlyFirst', 'type': 'Z'})
        self.assertNotIn('onlyFirst', [row['name'] for row in second['boundary']['tree']['binders']])

    def test_existing_trace_witnesses_bind_inside_the_same_scope(self):
        boundary, view = self.fixture()
        local = Expr('local', width=64, value='trace-owned-local')
        boundary['path_conditions'].append(operation('=', local, bits(1, 64)).to_dict())
        result = self.render(boundary, view)
        self.assertEqual(result['status'], 'rendered')
        self.assertEqual(len(result['trace_witnesses']), 1)
        for name in result['trace_witnesses']:
            self.assertIn('(' + name + ' : bv 64)', result['boundary']['body'])

    def test_unsupported_guard_is_explicit_and_never_completes(self):
        boundary, view = self.fixture()
        unsupported = operation('=', Expr('unknown_read', width=64, value='unbound'), bits(0, 64)).to_dict()
        boundary['path_conditions'].append(unsupported)
        result = self.render(boundary, view)
        self.assertEqual(result['status'], 'refused')
        self.assertEqual(result['refusals'][0]['expression'], unsupported)
        self.assertEqual(len(result['guards']), 1)
        self.assertFalse(result['proof_established'])


if __name__ == '__main__':
    unittest.main()
