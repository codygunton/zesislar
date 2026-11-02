"""Check return assertions without assigning generated-entry status."""
from copy import deepcopy
import unittest

from entry_formatter import SymbolicConditions
from return_assertion import format_return_assertion


class ReturnAssertionTests(unittest.TestCase):
    def resource(self):
        return {'block_status': 'completed', 'reports': [],
            'write_accounting': {'status': 'complete', 'writes': [{'offset': 3}]},
            'path_conditions': [{'op': '=', 'args': [
                {'op': 'input', 'width': 64, 'value': 'r'},
                {'op': 'bits', 'width': 64, 'value': 7}]}],
            'components': [{'id': 'owner', 'source': 'p ↦ₘ{DfracOwn q}∗ bytes'},
                           {'id': 'K', 'source': 'K'}],
            'tree': {'kind': 'sep', 'left': {'kind': 'exists',
                'binders': [{'name': 'r', 'type': 'bv 64'}],
                'body': {'kind': 'component', 'id': 'owner'}},
                'right': {'kind': 'component', 'id': 'K'}}}

    def run_format(self, resource=None, **kwargs):
        options = dict(source_binding={'path': '/frozen/FORWARD.json',
            'sha256': 'a' * 64, 'pointer': '/stops/0'}, pc='returnPC',
            continuation_id='K', guard_scope=(0,),
            condition_adapter=SymbolicConditions(lambda ctx: {'source': '/stops/0'},
                                                 normal_form=False))
        options.update(kwargs)
        return format_return_assertion(resource or self.resource(), **options)

    def test_preserves_source_ownership_scope_writes_and_continuation(self):
        resource = self.resource()
        original = deepcopy(resource)
        result = self.run_format(resource)
        self.assertEqual(result.reports, [])
        self.assertEqual(resource, original)
        self.assertIn('p ↦ₘ{DfracOwn q}∗ bytes', result.source)
        self.assertTrue(result.source.endswith(' ∗ K)'))
        self.assertIn('∃ (r : bv 64)', result.source)
        self.assertEqual(result.manifest['ordered_writes'], resource['write_accounting'])
        self.assertEqual(result.manifest['conditions'][0]['source'], resource['path_conditions'][0])
        self.assertNotIn('status', result.manifest)

    def test_accepts_unknown_pc_source_without_entry_status(self):
        result = self.run_format(source_binding={'path': '/frozen/FORWARD.json',
            'sha256': 'b' * 64, 'pointer': '/stops/0', 'stop_status': 'unknown_pc'})
        self.assertIsNotNone(result.source)
        self.assertEqual(result.manifest['source_binding']['stop_status'], 'unknown_pc')

    def test_typed_alias_requires_exact_scope(self):
        from symbolic_state import Expr
        value = Expr.from_dict({'op': 'input', 'width': 64, 'value': 'r'})
        adapter = SymbolicConditions(lambda ctx: {'source': '/stops/0'},
            aliases={value: 'system_r'}, normal_form=False)
        result = self.run_format(condition_adapter=adapter,
            scoped_binders=[{'name': 'system_r', 'type': 'bv 64'}])
        self.assertIsNotNone(result.source)
        self.assertIn('(system_r : bv 64)', result.source)
        result = self.run_format(condition_adapter=adapter,
            scoped_binders=[{'name': 'system_r', 'type': 'bool'}])
        self.assertIsNone(result.source)

    def test_refuses_missing_source_binding(self):
        self.assertIsNone(self.run_format(source_binding={}).source)

    def test_refuses_incomplete_resources(self):
        resource = self.resource(); resource['block_status'] = 'OPEN'
        self.assertIsNone(self.run_format(resource).source)

    def test_refuses_incomplete_writes(self):
        resource = self.resource(); resource['write_accounting']['status'] = 'OPEN'
        self.assertIsNone(self.run_format(resource).source)

    def test_refuses_changed_continuation_scope(self):
        resource = self.resource(); resource['tree']['right'] = resource['tree']['left']
        self.assertIsNone(self.run_format(resource).source)

    def test_refuses_missing_condition_scope(self):
        self.assertIsNone(self.run_format(guard_scope=(2,)).source)

    def test_refuses_nonexistential_condition_scope(self):
        self.assertIsNone(self.run_format(guard_scope=()).source)

    def test_refuses_repeated_owned_component(self):
        resource = self.resource(); leaf = resource['tree']['left']['body']
        resource['tree']['left']['body'] = {'kind': 'sep_list', 'children': [leaf, leaf]}
        self.assertIsNone(self.run_format(resource).source)

    def test_refuses_omitted_owned_component(self):
        resource = self.resource(); resource['components'].append({'id': 'extra', 'source': 'Q'})
        self.assertIsNone(self.run_format(resource).source)

    def test_refuses_unknown_condition_input(self):
        resource = self.resource()
        resource['path_conditions'] = [{'op': 'unknown_input', 'value': 'missing'}]
        self.assertIsNone(self.run_format(resource).source)

    def test_refuses_omitted_condition(self):
        self.assertIsNone(self.run_format(condition_adapter=lambda expr, ctx:
            {'components': [], 'existentials': []}).source)

    def test_refuses_shadowed_scoped_binder(self):
        self.assertIsNone(self.run_format(scoped_binders=[{'name': 'r', 'type': 'bv 64'}]).source)


if __name__ == '__main__':
    unittest.main()
