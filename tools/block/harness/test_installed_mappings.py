from pathlib import Path
import tempfile
import unittest

import scratch
from installed_mappings import InstalledMappings
from prospective_inputs import module_source


class InstalledMappingTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.theories = self.root / 'theories'
        self.user = self.root / 'user-contrib/example'
        self.theories.mkdir(parents=True)
        self.user.mkdir(parents=True)
        self.flags = ['-R', str(self.theories), 'Coq', '-Q', str(self.user), 'example']

    def library(self, root, relative):
        source = root / relative
        source.parent.mkdir(parents=True, exist_ok=True)
        source.write_text('Definition placeholder := 0.\n')
        source.with_suffix('.vo').write_bytes(b'object')
        return source.absolute()

    def mapping(self, statement=None, flags=None):
        installed = InstalledMappings(flags or self.flags, receipt_dir=self.root / 'receipts')
        if statement:
            origin = self.root / 'Import.v'
            origin.write_text(statement)
            installed.register_source(statement, origin)
        return installed

    def test_standard_library_root_alias_uses_exact_from_syntax(self):
        expected = self.library(self.theories, 'micromega/Lia.v')
        installed = self.mapping('From Coq Require Import Lia.')
        self.assertEqual(installed.resolve('Coq.Lia'), expected)
        self.assertTrue(list((self.root / 'receipts').glob('*.json')))
        self.assertEqual(installed.inventory()['resolutions'][0]['canonical_module'], 'Coq.micromega.Lia')

    def test_import_category_modifier_is_preserved(self):
        expected = self.library(self.theories, 'ssr/ssrfun.v')
        installed = self.mapping('From Coq.ssr Require Import (notations) ssrfun.')
        self.assertEqual(installed.resolve('Coq.ssr.ssrfun'), expected)
        self.assertEqual(installed.inventory()['resolutions'][0]['requests'],
                         ['From Coq.ssr Require Import ( notations ) ssrfun.\n'])

    def test_incomplete_import_category_modifier_refuses(self):
        with self.assertRaisesRegex(ValueError, 'unbalanced argument'):
            self.mapping('From Coq.ssr Require Import (notations ssrfun.')

    def test_list_alias_uses_exact_from_syntax(self):
        expected = self.library(self.theories, 'Lists/List.v')
        self.assertEqual(self.mapping('From Coq Require Import List.').resolve('Coq.List'), expected)

    def test_short_name_without_bound_from_syntax_refuses(self):
        self.library(self.theories, 'micromega/Lia.v')
        with self.assertRaisesRegex(ValueError, 'no bound source syntax'):
            self.mapping().resolve('Coq.Lia')

    def test_direct_require_does_not_invent_from_syntax(self):
        self.library(self.theories, 'micromega/Lia.v')
        with self.assertRaisesRegex(ValueError, 'no actual installed mapping'):
            self.mapping('Require Import Coq.Lia.').resolve('Coq.Lia')

    def test_nested_canonical_name_uses_coqdep(self):
        expected = self.library(self.theories, 'ZArith/BinInt.v')
        self.assertEqual(self.mapping().resolve('Coq.ZArith.BinInt'), expected)

    def test_user_contrib_module_uses_coqdep(self):
        expected = self.library(self.user, 'nested/Module.v')
        self.assertEqual(self.mapping().resolve('example.nested.Module'), expected)

    def test_user_contrib_from_syntax_uses_coqdep(self):
        expected = self.library(self.user, 'nested/Module.v')
        self.assertEqual(self.mapping('From example.nested Require Import Module.').resolve('example.nested.Module'), expected)

    def test_wrong_namespace_does_not_match(self):
        self.library(self.user, 'nested/Lia.v')
        with self.assertRaisesRegex(ValueError, 'no actual installed mapping'):
            self.mapping('From Coq Require Import Lia.').resolve('Coq.Lia')

    def test_duplicate_basenames_refuse_tool_warning(self):
        self.library(self.theories, 'first/Shared.v')
        self.library(self.theories, 'second/Shared.v')
        with self.assertRaisesRegex(ValueError, 'ambiguous'):
            self.mapping('From Coq Require Import Shared.').resolve('Coq.Shared')

    def test_full_qualification_resolves_duplicate_basenames(self):
        expected = self.library(self.theories, 'first/Shared.v')
        self.library(self.theories, 'second/Shared.v')
        self.assertEqual(self.mapping().resolve('Coq.first.Shared'), expected)

    def test_missing_object_does_not_create_a_mapping(self):
        source = self.theories / 'Missing.v'
        source.parent.mkdir(parents=True, exist_ok=True)
        source.write_text('Definition placeholder := 0.\n')
        with self.assertRaisesRegex(ValueError, 'object is absent'):
            self.mapping('From Coq Require Import Missing.').resolve('Coq.Missing')

    def test_overlapping_roots_deduplicate_actual_files(self):
        expected = self.library(self.user, 'nested/Module.v')
        flags = self.flags + ['-Q', str(self.user / 'nested'), 'example.nested']
        self.assertEqual(self.mapping(flags=flags).resolve('example.nested.Module'), expected)

    def test_inventory_binds_each_source_and_object_path(self):
        expected = self.library(self.user, 'nested/Module.v')
        inventory = self.mapping().inventory()
        module = next(row for row in inventory['modules'] if row['logical_module'] == 'example.nested.Module')
        self.assertEqual(module['source'], str(expected))
        self.assertEqual(module['object'], str(expected.with_suffix('.vo')))
        self.assertTrue(module['source_present'])

    def test_current_proof_source_needs_no_prior_object(self):
        source = self.root / 'Private.v'
        source.write_text('Definition placeholder := 0.\n')
        runtime = {'module_files': {'example.Module': 'Private.v'}, 'physical_flags': self.flags,
                   'target': {'block': {'module': 'example.Module'}}}
        self.assertEqual(module_source('example.Module', runtime, self.root), source)

    def test_private_import_must_match_compiler_resolution(self):
        self.library(self.user, 'Module.v')
        source = self.root / 'Private.v'
        source.write_text('Definition placeholder := 0.\n')
        runtime = {'module_files': {'example.Module': 'Private.v'}, 'physical_flags': self.flags,
                   'target': {'block': {'module': 'Current'}}}
        with self.assertRaisesRegex(ValueError, 'differs from its declared source'):
            module_source('example.Module', runtime, self.root, self.mapping())

    def test_new_import_requires_pinned_resolution(self):
        self.library(self.theories, 'micromega/Lia.v')
        installed = self.mapping()
        edges = scratch.canonical_edges('Private', 'From Coq Require Import Lia.', None, [], {}, installed)
        self.assertEqual(edges, [{'from': 'Private', 'to': 'Coq.micromega.Lia'}])
        with self.assertRaisesRegex(ValueError, 'no actual installed mapping'):
            scratch.canonical_edges('Private', 'From Coq Require Import Absent.', None, [], {}, installed)

    def test_inventory_is_stable_across_owned_workspace_paths(self):
        from stage1_runtime import installed_mapping_inventory
        first, second = self.root / 'first', self.root / 'second'
        for root in [first, second]:
            self.library(root, 'theories/micromega/Lia.v')
        a = InstalledMappings(['-R', str(first / 'theories'), 'Coq'])
        b = InstalledMappings(['-R', str(second / 'theories'), 'Coq'])
        common = [{'role': 'system', 'path': '/'}]
        left = installed_mapping_inventory(a, [{'role': 'workspace', 'path': str(first)}, *common])
        right = installed_mapping_inventory(b, [{'role': 'workspace', 'path': str(second)}, *common])
        self.assertEqual(left, right)

    def test_plain_require_is_recorded_without_inventing_an_import_modifier(self):
        expected = self.library(self.user, 'Module.v')
        self.assertEqual(self.mapping('Require example.Module.').resolve('example.Module'), expected)

    def test_failed_require_control_is_not_registered_as_a_real_import(self):
        installed = self.mapping('Fail Require Import Coq.Lia.')
        self.assertNotIn('Coq.Lia', installed.requests)

if __name__ == '__main__':
    unittest.main()
