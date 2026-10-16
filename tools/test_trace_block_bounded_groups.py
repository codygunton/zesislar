"""Preserve defined raw group members without inventing erased conclusions."""
from copy import deepcopy
from pathlib import Path
import sys
import unittest

sys.path.insert(0, str(Path(__file__).parent / 'block'))
from trace_block_bounded_capture import BoundedCapture, pointer
from trace_block_bounded_points import rollback_equal
from trace_block_bounded_bundle import markdown


class RawGroupTests(unittest.TestCase):
    def fixture(self, ids=(7, 8, 7), group='goals'):
        value = BoundedCapture.__new__(BoundedCapture)
        value.sidecar = {'path': 'complete.marshal', 'sha256': 'a' * 64, 'bytes': 100}
        value.catalog_ref = {'path': 'catalog.json', 'sha256': 'b' * 64, 'bytes': 200}
        body = {'availability': 'referenced', 'complete_sidecar': value.sidecar,
                'node_ref': {'root_id': 'evar/7/body', 'child_path': []}}
        value.catalog_indexes = {7: 0, 8: 1}
        value.by_id = {key: {'defined': key == 7, 'name': 'g%d' % key,
            'body': body if key == 7 else None, 'context': [], 'filter': []} for key in (7, 8)}
        rows = []
        for key in ids:
            rows.append({'evar': key, 'name': 'g%d' % key,
                'status': 'defined' if key == 7 else 'undefined',
                'entry_ref': {'catalog_ref': value.catalog_ref,
                              'pointer': '#/entries/%d' % value.catalog_indexes[key]},
                'conclusion': {'availability': 'unavailable',
                    'reason': 'Evd erases the conclusion of a defined evar'} if key == 7 else 'P',
                'display_ref': None if key == 7 else pointer('evar/8/conclusion'),
                'body': deepcopy(body) if key == 7 else None, 'hyps': []})
        groups = {name: rows if name == group else [] for name in ('goals', 'shelf', 'given_up')}
        value.catalog = {'schema': 1, 'complete_sidecar': value.sidecar,
                         'entries': [dict(value.by_id[key], id=key) for key in (7, 8)]}
        value.capture = {'evar_catalog_ref': value.catalog_ref, 'schema': 2, 'group_policy': 'raw-ordered-goals-v1',
            'group_counts': {name: len(entries) for name, entries in groups.items()},
            'complete_sidecar': value.sidecar, 'fresh_evar_counter': 20,
            'live_goal_ids': list(ids) if group == 'goals' else [],
            **{mode: dict(deepcopy(groups), hidden_stack={}) for mode in ('notation', 'no_notation')}}
        value._display = lambda name, reference, left, right: {'checked': name}
        return value

    def test_preserve_order_and_repetitions(self):
        value = self.fixture()
        rows = value._goals('goals')
        self.assertEqual([row['id'] for row in rows], [7, 8, 7])
        self.assertEqual([row['status'] for row in rows], ['defined', 'undefined', 'defined'])
        self.assertEqual(value.capture['group_counts']['goals'], 3)

    def test_defined_body_is_not_a_conclusion(self):
        value = self.fixture((7,))
        row = value._goals('goals')[0]
        self.assertIsNone(row['goal'])
        self.assertIsNone(row['goal_nonotation'])
        self.assertIsNone(row['term'])
        self.assertEqual(row['body'], value.by_id[7]['body'])
        self.assertEqual(row['goal_availability']['availability'], 'unavailable')
        self.assertEqual(row['entry_ref']['pointer'], '#/entries/0')

    def test_defined_members_in_all_groups(self):
        for group in ('goals', 'shelf', 'given_up'):
            with self.subTest(group=group):
                self.assertEqual([row['id'] for row in self.fixture((7, 7), group)._goals(group)], [7, 7])

    def reject(self, edit):
        value = self.fixture((7, 8))
        edit(value)
        with self.assertRaises((ValueError, KeyError)):
            value._goals('goals')

    def test_wrong_count_rejects(self):
        self.reject(lambda value: value.capture['group_counts'].update(goals=1))

    def test_boolean_count_rejects(self):
        self.reject(lambda value: value.capture['group_counts'].update(goals=True))

    def test_changed_status_rejects(self):
        self.reject(lambda value: value.capture['notation']['goals'][0].update(status='undefined'))

    def test_foreign_catalog_index_rejects(self):
        self.reject(lambda value: value.capture['notation']['goals'][0]['entry_ref'].update(pointer='#/entries/1'))

    def test_foreign_catalog_reference_rejects(self):
        self.reject(lambda value: value.capture['notation']['goals'][0]['entry_ref']['catalog_ref'].update(sha256='c' * 64))

    def test_missing_body_rejects(self):
        self.reject(lambda value: value.capture['notation']['goals'][0].update(body=None))

    def test_body_substitution_rejects(self):
        self.reject(lambda value: value.capture['notation']['goals'][0]['body']['node_ref'].update(root_id='evar/8/body'))

    def test_invented_conclusion_rejects(self):
        self.reject(lambda value: value.capture['notation']['goals'][0].update(conclusion='True'))

    def test_body_display_as_conclusion_rejects(self):
        self.reject(lambda value: value.capture['notation']['goals'][0].update(display_ref=pointer('evar/7/body')))

    def test_cross_mode_status_rejects(self):
        self.reject(lambda value: value.capture['no_notation']['goals'][0].update(status='undefined'))

    def test_cross_mode_order_rejects(self):
        self.reject(lambda value: value.capture['no_notation']['goals'].reverse())

    def test_undefined_body_rejects(self):
        self.reject(lambda value: value.capture['notation']['goals'][1].update(body=value.by_id[7]['body']))

    def test_schema1_keeps_exact_undefined_rows(self):
        value = self.fixture((8,))
        value.capture['schema'] = 1
        for mode in ('notation', 'no_notation'):
            for field in ('status', 'entry_ref', 'body'):
                value.capture[mode]['goals'][0].pop(field)
        self.assertEqual(set(value._goals('goals')[0]), {'id', 'goal', 'goal_nonotation', 'hyps', 'term'})

    def test_schema1_still_rejects_defined_row(self):
        value = self.fixture((7,))
        value.capture['schema'] = 1
        for mode in ('notation', 'no_notation'):
            for field in ('status', 'entry_ref', 'body'):
                value.capture[mode]['goals'][0].pop(field)
        with self.assertRaises(ValueError):
            value._goals('goals')

    def test_rollback_compares_status(self):
        value = self.fixture()
        before = value.capture
        after = deepcopy(before)
        catalogs = {'before_catalog': value.catalog, 'after_catalog': deepcopy(value.catalog)}
        self.assertTrue(rollback_equal(before, after, **catalogs))
        after['notation']['goals'][0]['status'] = 'undefined'
        self.assertFalse(rollback_equal(before, after, **catalogs))

    def test_rollback_compares_body_reference(self):
        value = self.fixture()
        before = value.capture
        after = deepcopy(before)
        catalogs = {'before_catalog': value.catalog, 'after_catalog': deepcopy(value.catalog)}
        after['no_notation']['goals'][0]['body']['node_ref']['root_id'] = 'foreign'
        self.assertFalse(rollback_equal(before, after, **catalogs))

    def test_rollback_compares_counts(self):
        value = self.fixture()
        before = value.capture
        after = deepcopy(before)
        catalogs = {'before_catalog': value.catalog, 'after_catalog': deepcopy(value.catalog)}
        after['group_counts']['goals'] = 0
        self.assertFalse(rollback_equal(before, after, **catalogs))

    def test_schema2_without_checked_catalogs_rejects(self):
        value = self.fixture()
        self.assertFalse(rollback_equal(value.capture, deepcopy(value.capture)))

    def relocated(self):
        value = self.fixture()
        before = value.capture
        after = deepcopy(before)
        after['complete_sidecar']['path'] = 'rollback/complete.marshal'
        after['evar_catalog_ref'].update(path='rollback/catalog.json', sha256='c' * 64)
        catalog = deepcopy(value.catalog)
        catalog['complete_sidecar'] = deepcopy(after['complete_sidecar'])
        for entry in catalog['entries']:
            if entry['body'] is not None:
                entry['body']['complete_sidecar'] = deepcopy(after['complete_sidecar'])
        for mode in ('notation', 'no_notation'):
            for group in ('goals', 'shelf', 'given_up'):
                for row in after[mode][group]:
                    row['entry_ref']['catalog_ref'] = deepcopy(after['evar_catalog_ref'])
                    if row['body'] is not None:
                        row['body']['complete_sidecar'] = deepcopy(after['complete_sidecar'])
        return before, after, {'before_catalog': value.catalog, 'after_catalog': catalog}

    def test_exact_local_references_allow_distinct_event_paths(self):
        before, after, catalogs = self.relocated()
        self.assertTrue(rollback_equal(before, after, **catalogs))

    def test_foreign_group_catalog_reference_rejects(self):
        before, after, catalogs = self.relocated()
        after['notation']['goals'][0]['entry_ref']['catalog_ref']['path'] = 'foreign.json'
        self.assertFalse(rollback_equal(before, after, **catalogs))

    def test_foreign_catalog_body_sidecar_rejects(self):
        before, after, catalogs = self.relocated()
        catalogs['after_catalog']['entries'][0]['body']['complete_sidecar']['path'] = 'foreign.marshal'
        self.assertFalse(rollback_equal(before, after, **catalogs))

    def test_substituted_raw_body_rejects(self):
        before, after, catalogs = self.relocated()
        after['notation']['goals'][0]['body']['node_ref']['root_id'] = 'evar/8/body'
        self.assertFalse(rollback_equal(before, after, **catalogs))

    def test_catalog_status_change_rejects(self):
        before, after, catalogs = self.relocated()
        catalogs['after_catalog']['entries'][0]['defined'] = False
        self.assertFalse(rollback_equal(before, after, **catalogs))

    def test_catalog_context_change_rejects(self):
        before, after, catalogs = self.relocated()
        catalogs['after_catalog']['entries'][0]['context'] = [{'name': 'foreign'}]
        self.assertFalse(rollback_equal(before, after, **catalogs))

    def test_catalog_filter_change_rejects(self):
        before, after, catalogs = self.relocated()
        catalogs['after_catalog']['entries'][0]['filter'] = [False]
        self.assertFalse(rollback_equal(before, after, **catalogs))

    def test_catalog_name_change_rejects(self):
        before, after, catalogs = self.relocated()
        catalogs['after_catalog']['entries'][0]['name'] = 'foreign'
        self.assertFalse(rollback_equal(before, after, **catalogs))

    def test_catalog_entry_order_change_rejects(self):
        before, after, catalogs = self.relocated()
        catalogs['after_catalog']['entries'].reverse()
        self.assertFalse(rollback_equal(before, after, **catalogs))

    def test_group_pointer_substitution_rejects(self):
        before, after, catalogs = self.relocated()
        after['notation']['goals'][0]['entry_ref']['pointer'] = '#/entries/1'
        self.assertFalse(rollback_equal(before, after, **catalogs))

    def test_renderer_marks_erased_conclusion_unavailable(self):
        value = self.fixture((7,))._goals('goals')[0]
        point = dict(value, trigger={'rule': 'Control'}, hand_call=[])
        output = ''.join(markdown({'completion': {'trace_complete': False, 'reasons': []},
                                  'points': [point], 'residual': None}))
        self.assertIn('erased conclusion is unavailable', output)
        self.assertNotIn('```rocq', output)

    def test_renderer_rejects_unsupported_missing_goal(self):
        point = {'goal': None, 'trigger': {'rule': 'Control'}, 'hand_call': []}
        with self.assertRaises(ValueError):
            ''.join(markdown({'completion': {'trace_complete': False, 'reasons': []},
                              'points': [point], 'residual': None}))


if __name__ == '__main__':
    unittest.main()
