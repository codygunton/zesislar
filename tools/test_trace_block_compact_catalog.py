"""Check compact catalog associations without running a Marshal reader."""
from copy import deepcopy
from pathlib import Path
import sys
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).parent / 'block'))
from trace_block_compact_catalog import catalog_header, descriptor, receipt_check
from trace_block_bounded_capture import BoundedCapture
from trace_block_bounded_points import _catalog_equal
from trace_block_kernel_display import _reload, RELOAD_CHECKS


class CompactCatalogTests(unittest.TestCase):
    def fixture(self):
        sidecar = {'path': 'complete.marshal', 'sha256': 'a' * 64, 'bytes': 99}
        catalog = {'schema': 2, 'complete_sidecar': sidecar, 'selected_ids': [2], 'entries': []}
        groups = {'goals': [2, 2], 'shelf': [], 'given_up': []}
        return sidecar, catalog, groups

    def test_sorted_raw_union_preserves_repetitions_elsewhere(self):
        sidecar, catalog, groups = self.fixture()
        self.assertEqual(catalog_header(catalog, sidecar, groups), 2)
        self.assertEqual(groups['goals'], [2, 2])

    def test_historical_header(self):
        sidecar, catalog, groups = self.fixture()
        catalog.pop('selected_ids'); catalog['schema'] = 1
        self.assertEqual(catalog_header(catalog, sidecar, groups), 1)

    def test_header_substitutions_reject(self):
        edits = [lambda c: c.update(schema=True), lambda c: c.update(schema=3),
                 lambda c: c.update(extra=True), lambda c: c.pop('selected_ids'),
                 lambda c: c.update(selected_ids=[True]), lambda c: c.update(selected_ids=[2, 2]),
                 lambda c: c.update(selected_ids=[3]), lambda c: c.update(entries={}),
                 lambda c: c['complete_sidecar'].update(path='foreign')]
        for edit in edits:
            with self.subTest(edit=edit):
                sidecar, catalog, groups = self.fixture(); sidecar = deepcopy(sidecar); edit(catalog)
                with self.assertRaises(ValueError): catalog_header(catalog, sidecar, groups)

    def reference(self, sidecar, field='context', count=3):
        return {'availability': 'referenced', 'complete_sidecar': sidecar,
                'catalog_index': 0, 'evar': 1, 'field': field, 'count': count}

    def test_exact_descriptor(self):
        sidecar, _, _ = self.fixture()
        for field in ('context', 'filter'):
            descriptor(self.reference(sidecar, field), sidecar, 0, 1, field, 3)

    def test_descriptor_substitutions_reject(self):
        sidecar, _, _ = self.fixture()
        edits = [lambda d: d.update(extra=True), lambda d: d.update(availability='complete'),
                 lambda d: d.update(catalog_index=1), lambda d: d.update(catalog_index=False),
                 lambda d: d.update(evar=2), lambda d: d.update(evar=True),
                 lambda d: d.update(field='filter'), lambda d: d.update(count=4),
                 lambda d: d.update(count=True), lambda d: d['complete_sidecar'].update(sha256='b' * 64)]
        for edit in edits:
            with self.subTest(edit=edit):
                value = deepcopy(self.reference(sidecar)); edit(value)
                with self.assertRaises(ValueError): descriptor(value, sidecar, 0, 1, 'context', 3)

    def receipt(self, catalog):
        return {'schema': 2, 'entries': len(catalog['entries']), 'selected_ids': [2],
                'referenced_contexts': len(catalog['entries']) - 1,
                'referenced_filters': len(catalog['entries']) - 1,
                'complete': True, 'verification': 'compact-catalog-to-Marshal'}

    def test_complete_receipt(self):
        _, catalog, _ = self.fixture(); catalog['entries'] = [{}, {}]
        receipt_check(self.receipt(catalog), catalog)

    def test_receipt_substitutions_reject(self):
        _, catalog, _ = self.fixture(); catalog['entries'] = [{}, {}]
        edits = [lambda r: r.update(extra=True), lambda r: r.update(schema=True),
                 lambda r: r.update(entries=1), lambda r: r.update(selected_ids=[True]),
                 lambda r: r.update(selected_ids=[3]), lambda r: r.update(referenced_contexts=0),
                 lambda r: r.update(referenced_filters=0), lambda r: r.update(complete=False),
                 lambda r: r.update(verification='metadata-only')]
        for edit in edits:
            with self.subTest(edit=edit):
                value = self.receipt(catalog); edit(value)
                with self.assertRaises(ValueError): receipt_check(value, catalog)

    def evars(self):
        value = BoundedCapture.__new__(BoundedCapture)
        value.sidecar, value.catalog, groups = self.fixture()
        value.catalog_ref = {'path': 'catalog.json', 'sha256': 'b' * 64, 'bytes': 200}
        def term(name):
            return {'availability': 'referenced', 'complete_sidecar': value.sidecar,
                    'node_ref': {'root_id': name, 'child_path': []}}
        rows, compact = [], []
        for index, key in enumerate((1, 2)):
            defined = key == 1
            row = {'id': key, 'name': 'g%d' % key, 'defined': defined,
                   'type': {'availability': 'unavailable', 'reason': 'Evd erases the conclusion of a defined evar'}
                           if defined else term('evar/2/conclusion'),
                   'body': term('evar/1/body') if defined else None,
                   'context': self.reference(value.sidecar, count=3) if defined else [],
                   'filter': self.reference(value.sidecar, 'filter', 3) if defined else [],
                   'context_declarations': 3 if defined else 0,
                   'candidates': None, 'candidate_count': None}
            rows.append(row)
            compact.append({'id': key, 'defined': defined, 'body': row['body'],
                            'type': {'availability': 'unavailable', 'reason': 'Evd erases defined conclusions'}
                                    if defined else row['type'],
                            'context': {'catalog_ref': value.catalog_ref, 'pointer': '#/entries/%d/context' % index},
                            'entry_ref': {'catalog_ref': value.catalog_ref, 'pointer': '#/entries/%d' % index}})
        value.catalog['entries'] = rows
        value.capture = {'evars': compact}
        catalog_header(value.catalog, value.sidecar, groups)
        return value

    def test_all_entries_and_references_remain(self):
        value = self.evars(); value._evars()
        self.assertEqual([entry['id'] for entry in value.entries], [1, 2])
        self.assertEqual(value.entries[0]['status'], 'defined')
        self.assertEqual(value.entries[0]['filter']['count'], 3)
        self.assertEqual(value.entries[0]['body']['node_ref']['root_id'], 'evar/1/body')

    def test_selected_descriptor_rejects(self):
        value = self.evars(); value.catalog['selected_ids'] = [1, 2]
        with self.assertRaises(ValueError): value._evars()

    def test_nonselected_inline_context_rejects(self):
        value = self.evars(); value.catalog['entries'][0]['context'] = []
        with self.assertRaises(ValueError): value._evars()

    def test_filter_count_substitution_rejects(self):
        value = self.evars(); value.catalog['entries'][0]['filter']['count'] = 2
        with self.assertRaises(ValueError): value._evars()

    def test_missing_selected_catalog_entry_rejects(self):
        value = self.evars(); value.catalog['selected_ids'] = [2, 3]
        with self.assertRaises(ValueError): value._evars()

    def test_catalog_comparison_checks_compact_fields(self):
        value = self.evars(); value._evars(); right = deepcopy(value.catalog)
        after = {'complete_sidecar': deepcopy(value.sidecar)}
        after['complete_sidecar']['path'] = 'rollback/complete.marshal'
        def relocate(item):
            if isinstance(item, dict):
                for key, field in item.items():
                    if key == 'complete_sidecar': item[key] = deepcopy(after['complete_sidecar'])
                    else: relocate(field)
            elif isinstance(item, list):
                for child in item: relocate(child)
        relocate(right)
        before = {'complete_sidecar': value.sidecar}
        self.assertTrue(_catalog_equal(value.catalog, right, before, after))
        right['entries'][0]['filter']['count'] = 2
        self.assertFalse(_catalog_equal(value.catalog, right, before, after))

    def test_compact_reload_requires_receipt_and_context_join(self):
        sidecar, catalog, groups = self.fixture(); catalog['entries'] = [{}, {}]
        display = {'complete_sidecar': sidecar, 'context_ref': 'context',
                   'evar_catalog_ref': 'catalog', 'toolchain_ref': 'toolchain'}
        receipt = {'schema': 1, 'kind': 'kernel-marshal-reload', 'sidecar': sidecar,
                   'context_ref': 'context', 'evar_catalog_ref': 'catalog',
                   'toolchain_ref': 'toolchain', 'reader': 'reader', 'accepted': True,
                   'checks': {key: True for key in RELOAD_CHECKS}, 'kernel_typecheck': 'not-attempted',
                   'error': None, 'unique_kernel_nodes': 1, 'catalog_check': self.receipt(catalog)}
        context = dict(groups, schema=1, kind='kernel-snapshot-context', complete_sidecar=sidecar)
        records = {'catalog': catalog, 'context': context, 'receipt': receipt}
        with patch('trace_block_kernel_display._read', side_effect=lambda root, ref: records[ref]):
            self.assertIs(_reload(None, 'receipt', display, 'reader'), receipt)
            receipt.pop('catalog_check')
            with self.assertRaises(ValueError): _reload(None, 'receipt', display, 'reader')
            receipt['catalog_check'] = self.receipt(catalog); context['shelf'] = [1]
            with self.assertRaises(ValueError): _reload(None, 'receipt', display, 'reader')


if __name__ == '__main__':
    unittest.main()
