"""Declaration adapters preserve alternatives, ownership, and continuation scope."""
from copy import deepcopy
import hashlib
from pathlib import Path
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parent / 'block'))
from coq_scopes import z_address_scope
from entry_formatter import SourceComponents, SymbolicConditions, format_entry_boundary
from fractional_source import FractionalSourceArrays, array_declaration
from guard_normal_form import GuardNormalForm
from forward_resources import _render_tree
from symbolic_state import Expr, bits, input_expr, operation


def origin(*_):
    return {'from_block': 'source-block', 'from_instruction': 'source-instruction'}


def boundary():
    tree = {'kind': 'sep', 'left': {'kind': 'exists',
            'binders': [{'name': 'value', 'type': 'bv 64'}],
            'body': {'kind': 'sep_list', 'children': [
                {'kind': 'component', 'id': 'register'},
                {'kind': 'component', 'id': 'array'},
                {'kind': 'component', 'id': 'terminal'}]}},
            'right': {'kind': 'component', 'id': 'K'}}
    resource = {'block_status': 'completed', 'tree': tree,
                'components': [{'id': 'register', 'source': '"x1" ↦ᵣ RVal_Bits value'},
                               {'id': 'array', 'source': 'base ↦ₘ∗ bytes'},
                               {'id': 'terminal', 'source': 'True'},
                               {'id': 'K', 'source': 'K'}],
                'path_conditions': [operation('=', input_expr('value', 64), bits(1, 64)).to_dict()]}
    return {'pc': 'source-pc', 'status': 'generated', 'alternatives': [
        {'path': [0], 'resource_boundary': deepcopy(resource)},
        {'path': [1], 'resource_boundary': deepcopy(resource)}]}


class FormatterTests(unittest.TestCase):
    def rendered_boundary(self):
        value = boundary()
        for alternative in value['alternatives']:
            resource = alternative['resource_boundary']
            resource['body'] = _render_tree(resource['tree'],
                {row['id']: row['source'] for row in resource['components']})
        return value

    def components(self):
        return SourceComponents({'K': {'owner': 'parameter', 'name': 'K'}},
                                continuation_id='K', provenance=origin)

    def formatted(self, value):
        return format_entry_boundary(value, case_id='source-case', source_policy='source-only',
            handwritten_owner='source-owner', continuation_id='K', guard_scope=(0,),
            component_adapter=self.components(), condition_adapter=SymbolicConditions(origin),
            helper_arguments=lambda *_: [], scoped_binders=())

    def test_all_alternatives_and_outer_continuation_remain(self):
        value = boundary()
        before = deepcopy(value)
        result = self.formatted(value)
        self.assertEqual(result.status, 'complete')
        self.assertEqual(result.manifest['alternative_count'], 2)
        body = result.response['body']
        self.assertEqual(body['components'][0]['kind'], 'disjunction')
        self.assertEqual(len(body['components'][0]['alternatives']), 2)
        self.assertEqual(body['components'][1]['kind'], 'continuation')
        self.assertEqual(body['components'][1]['predicate']['name'], 'K')
        self.assertEqual(value, before)
        self.assertFalse(result.manifest['proof_ran'])

    def test_exact_rendered_duplicates_keep_all_sources_and_one_entry(self):
        value = self.rendered_boundary()
        value['alternatives'] *= 2
        before = deepcopy(value)
        result = self.formatted(value)
        self.assertEqual(result.status, 'complete')
        self.assertEqual(result.manifest['alternative_count'], 4)
        self.assertEqual(result.manifest['emitted_alternative_count'], 1)
        self.assertEqual(len(result.manifest['exact_duplicate_alternatives']), 3)
        self.assertEqual(len(result.response['body']['additional_definitions']), 1)
        self.assertEqual(result.response['body']['components'][0]['kind'], 'application')
        self.assertEqual(result.response['body']['components'][1]['predicate']['name'], 'K')
        self.assertEqual(value, before)

    def test_rendered_resource_byte_difference_prevents_dedup(self):
        value = self.rendered_boundary()
        value['alternatives'][1]['resource_boundary']['body'] += ' '
        result = self.formatted(value)
        self.assertEqual(result.status, 'complete')
        self.assertEqual(result.manifest['emitted_alternative_count'], 2)

    def test_guard_difference_prevents_dedup(self):
        value = self.rendered_boundary()
        value['alternatives'][1]['resource_boundary']['path_conditions'] = [
            operation('=', input_expr('value', 64), bits(2, 64)).to_dict()]
        result = self.formatted(value)
        self.assertEqual(result.status, 'complete')
        self.assertEqual(result.manifest['emitted_alternative_count'], 2)

    def test_any_difference_preserves_even_the_identical_subset(self):
        value = self.rendered_boundary()
        value['alternatives'] = [deepcopy(value['alternatives'][0]) for _ in range(4)]
        value['alternatives'][3]['resource_boundary']['body'] += ' '
        result = self.formatted(value)
        self.assertEqual(result.status, 'complete')
        self.assertEqual(result.manifest['emitted_alternative_count'], 4)
        self.assertFalse(result.manifest['exact_deduplication']['all_alternatives_byte_identical'])
        self.assertEqual(result.manifest['exact_duplicate_alternatives'], [])

    def test_authored_resource_difference_prevents_dedup_with_stale_body(self):
        value = self.rendered_boundary()
        resource = value['alternatives'][1]['resource_boundary']
        resource['components'][0]['source'] = '"x2" ↦ᵣ RVal_Bits value'
        result = self.formatted(value)
        self.assertEqual(result.status, 'complete')
        self.assertEqual(result.manifest['emitted_alternative_count'], 2)

    def test_duplicate_candidate_still_validates_incomplete_source(self):
        value = self.rendered_boundary()
        value['alternatives'][1]['resource_boundary']['block_status'] = 'stopped'
        self.assertEqual(self.formatted(value).status, 'stopped')

    def test_duplicate_candidate_preserves_continuation_refusal(self):
        value = self.rendered_boundary()
        value['alternatives'][1]['resource_boundary']['components'][-1]['source'] = 'OtherK'
        self.assertEqual(self.formatted(value).status, 'stopped')

    def test_one_failed_alternative_refuses_the_complete_answer(self):
        value = boundary()
        value['alternatives'][1]['resource_boundary']['block_status'] = 'stopped'
        self.assertEqual(self.formatted(value).status, 'stopped')

    def test_changed_continuation_refuses(self):
        value = boundary()
        value['alternatives'][1]['resource_boundary']['components'][-1]['source'] = 'OtherK'
        self.assertEqual(self.formatted(value).status, 'stopped')

    def test_join_renders_only_the_generated_seed(self):
        value = boundary()
        value['status'] = 'generated_join'
        incoming, seed = value['alternatives']
        incoming.update(predecessor_pc='predecessor', seed_pc='function-entry')
        seed.update(predecessor_pc=None, seed_pc=value['pc'])
        result = self.formatted(value)
        self.assertEqual(result.status, 'complete')
        self.assertEqual(result.manifest['alternative_count'], 1)
        self.assertEqual(result.manifest['incoming_alternative_count'], 1)

    def test_join_without_a_generated_seed_refuses(self):
        value = boundary()
        value['status'] = 'generated_join'
        self.assertEqual(self.formatted(value).status, 'stopped')

    def test_changed_continuation_scope_refuses(self):
        value = boundary()
        value['alternatives'][0]['resource_boundary']['tree']['right'] = {'kind': 'component', 'id': 'terminal'}
        self.assertEqual(self.formatted(value).status, 'stopped')

    def test_duplicate_owned_component_refuses(self):
        value = boundary()
        resource = value['alternatives'][0]['resource_boundary']
        resource['components'].append(deepcopy(resource['components'][0]))
        self.assertEqual(self.formatted(value).status, 'stopped')

    def test_unknown_read_has_no_invented_binding(self):
        adapter = SymbolicConditions(origin)
        expression = operation('=', Expr('unknown_read', width=64), bits(0, 64))
        with self.assertRaisesRegex(ValueError, 'no source binding'):
            adapter(expression.to_dict(), {'binders': []})

    def test_trace_witness_keeps_type_and_provenance(self):
        adapter = SymbolicConditions(origin, normal_form=False)
        expression = operation('=', Expr('local', width=8, value='trace-byte'), bits(7, 8))
        result = adapter(expression.to_dict(), {'binders': []})
        self.assertEqual(result['existentials'][0]['type'], 'bv 8')
        self.assertEqual(result['components'][0]['terms'][0]['provenance'], origin())

    def test_source_alias_requires_its_original_typed_scope(self):
        witness = input_expr('source-value', 64)
        adapter = SymbolicConditions(origin, aliases={witness: 'value'})
        with self.assertRaisesRegex(ValueError, 'matching scoped binder'):
            adapter(operation('=', witness, bits(0, 64)).to_dict(), {'binders': []})

    def test_unbound_opaque_resource_refuses(self):
        with self.assertRaisesRegex(ValueError, 'no owner binding'):
            self.components()({'id': 'opaque', 'source': 'unknownPredicate args'}, {})

    def test_explicit_fraction_cannot_use_the_compact_adapter(self):
        with self.assertRaisesRegex(ValueError, 'explicit fraction'):
            self.components()({'id': 'array', 'source': 'base ↦ₘ{q}∗ bytes'}, {})


class FractionTests(unittest.TestCase):
    def setUp(self):
        self.directory = tempfile.TemporaryDirectory()
        self.addCleanup(self.directory.cleanup)
        self.path = Path(self.directory.name) / 'Source.v'
        self.path.write_text('Definition mem_mapsto_array_def := source_array.\n')
        source = {'path': str(self.path), 'sha256': hashlib.sha256(self.path.read_bytes()).hexdigest(),
                  'declaration': 'mem_mapsto_array_def'}
        self.declaration = {'owner': 'isla.ghost_state', 'name': 'mem_mapsto_array_def',
            'arguments': ['implicit n : N', 'a : Z', 'q : dfrac', 'l : list (bv n)'], 'source': source}

    def test_fraction_and_original_array_are_preserved(self):
        adapter = FractionalSourceArrays(lambda *_: [], declaration=self.declaration)
        result = adapter({'id': 'bytes', 'source': '(base + offset) ↦ₘ{q}∗ bytes'}, {'binders': []})
        self.assertEqual(result[0]['arguments'], ['((base + offset))%Z', '(q)', 'bytes'])
        self.assertEqual(adapter.applications[0]['fraction'], '{q}')
        self.assertFalse(adapter.applications[0]['proof_checked'])

    def test_fractional_scalar_refuses(self):
        plain = SourceComponents({}, continuation_id='K', provenance=origin)
        adapter = FractionalSourceArrays(plain, declaration=self.declaration)
        with self.assertRaisesRegex(ValueError, 'no owner binding'):
            adapter({'id': 'scalar', 'source': 'base ↦ₘ{q} value'}, {})

    def test_nonarray_delegation_preserves_the_full_fractional_source(self):
        received = []
        def plain(record, context):
            received.append(record['source'])
            return [{'kind': 'opaque', 'source': record['source']}]
        adapter = FractionalSourceArrays(plain, declaration=self.declaration)
        original = 'base ↦ₘ{q} value'
        result = adapter({'id': 'scalar', 'source': original}, {})
        self.assertEqual(received, [original])
        self.assertEqual(result[0]['source'], original)

    def test_changed_source_hash_refuses(self):
        vocabulary = {'input_sha256': 'fixture', 'rows': [{'kind': 'owned_byte_array', 'helper': self.declaration}]}
        self.path.write_text('Definition mem_mapsto_array_def := changed_array.\n')
        with self.assertRaisesRegex(ValueError, 'source changed'):
            array_declaration(vocabulary)

    def test_wrong_argument_order_refuses(self):
        declaration = deepcopy(self.declaration)
        declaration['arguments'][1:3] = reversed(declaration['arguments'][1:3])
        with self.assertRaisesRegex(ValueError, 'argument order'):
            FractionalSourceArrays(lambda *_: [], declaration=declaration)


class ScopeAndGuardTests(unittest.TestCase):
    def test_only_address_arithmetic_gets_Z_scope(self):
        self.assertEqual(z_address_scope('base + offset'), '(base + offset)%Z')
        self.assertEqual(z_address_scope('base'), 'base')

    def test_mask_does_not_prove_its_own_nonwrap_condition(self):
        word = input_expr('word', 64)
        wrapped = operation('bvand', operation('bvadd', word, bits(9, 64)), bits(255, 64))
        result = GuardNormalForm().render(operation('=', wrapped, bits(0, 64)))
        self.assertIn(wrapped.coq(), result['proposition'])
        self.assertEqual(result['requirements'][0]['kind'], 'missing_mask_range')
        self.assertEqual(result['requirements'][0]['available_interval'], [0, 2**64 - 1])
        self.assertFalse(result['rewrites'])
        self.assertNotIn('247', result['proposition'])

    def test_masked_result_condition_does_not_supply_the_base_range(self):
        word = input_expr('word', 64)
        wrapped = operation('bvand', operation('bvadd', word, bits(9, 64)), bits(255, 64))
        condition = operation('=', wrapped, bits(0, 64))
        result = GuardNormalForm([condition]).render(condition)
        self.assertIn(wrapped.coq(), result['proposition'])
        self.assertEqual(result['requirements'][0]['kind'], 'missing_mask_range')
        self.assertFalse(result['rewrites'])

    def test_existing_base_bounds_permit_the_one_wrap_view(self):
        word = input_expr('word', 64)
        wrapped = operation('bvand', operation('bvadd', word, bits(9, 64)), bits(255, 64))
        bounds = [operation('bvuge', word, bits(248, 64)),
                  operation('bvule', word, bits(255, 64))]
        result = GuardNormalForm(bounds).render(operation('=', wrapped, bits(0, 64)))
        self.assertIn('247', result['proposition'])
        self.assertFalse(result['requirements'])
        self.assertTrue(result['rewrites'])


if __name__ == '__main__':
    unittest.main()
