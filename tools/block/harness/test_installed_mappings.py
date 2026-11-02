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

    def test_stage_uses_exact_modifier_aware_library(self):
        expected = self.library(self.theories, 'ssr/ssrfun.v')
        text = 'From Coq.ssr Require Import (notations) ssrfun.'
        installed = self.mapping(text)
        edges = scratch.canonical_edges('Consumer', text, text, [], {}, installed)
        self.assertEqual(edges, [{'from': 'Consumer', 'to': 'Coq.ssr.ssrfun'}])
        self.assertEqual(installed.resolutions['Coq.ssr.ssrfun']['source'], expected)
        self.assertNotIn('Coq.ssr.notations', installed.resolutions)

    def test_stage_still_refuses_unresolved_library_with_modifier(self):
        text = 'From Coq.ssr Require Import (notations) missing.'
        installed = self.mapping(text)
        with self.assertRaises(ValueError):
            scratch.canonical_edges('Consumer', text, text, [], {}, installed)
        self.assertNotIn('Coq.ssr.missing', installed.resolutions)

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

    def test_owned_source_only_Q_and_R_use_coqdep_selection(self):
        for flag in ['-Q', '-R']:
            with self.subTest(flag=flag):
                source = self.user / 'nested/Values.v'
                source.parent.mkdir(exist_ok=True)
                source.write_text('Definition value := 0.\n')
                origin = self.user / 'Consumer.v'
                origin.write_text('From example.nested Require Import Values.\n')
                modules = {'example.nested.Values': str(source)}
                installed = InstalledMappings([flag, str(self.user), 'example'],
                    planning_workspace=self.root, source_files=modules)
                installed.register_source(origin.read_text(), origin)
                value = installed.source_resolution('example.nested.Values', modules, origin=origin)
                self.assertEqual(value['source'], source)
                self.assertEqual(value['canonical'], 'example.nested.Values')
                self.assertTrue(value['source_only'])
                self.assertFalse(source.with_suffix('.vo').exists())
                with self.assertRaisesRegex(ValueError, 'object is absent'):
                    installed.resolve('example.nested.Values', origin=origin)

    def test_owned_sail_sibling_source_without_object(self):
        source = self.user / 'Values.v'
        source.write_text('Definition value := 0.\n')
        origin = self.user / 'Real.v'
        origin.write_text('Require Import Values.\n')
        modules = {'SailStdpp.Values': str(source)}
        installed = InstalledMappings(['-Q', str(self.user), 'SailStdpp'],
            planning_workspace=self.root, source_files=modules)
        installed.register_source(origin.read_text(), origin)
        edges = scratch.canonical_edges('SailStdpp.Real', origin.read_text(), None,
                                        [], modules, installed, origin)
        self.assertEqual(edges, [{'from': 'SailStdpp.Real', 'to': 'SailStdpp.Values'}])
        self.assertFalse(source.with_suffix('.vo').exists())

    def test_owned_source_mapping_must_match_selected_namespace(self):
        source = self.user / 'Values.v'
        source.write_text('Definition value := 0.\n')
        origin = self.root / 'Consumer.v'
        origin.write_text('Require Import example.Values.\n')
        installed = InstalledMappings(self.flags, planning_workspace=self.root)
        installed.register_source(origin.read_text(), origin)
        with self.assertRaisesRegex(ValueError, 'one exact owned module'):
            installed.source_resolution('example.Values', {'Wrong.Values': str(source)}, origin=origin)

    def test_external_source_only_is_not_an_owned_plan(self):
        source = self.theories / 'Missing.v'
        source.write_text('Definition value := 0.\n')
        origin = self.user / 'Consumer.v'
        origin.write_text('From Coq Require Import Missing.\n')
        installed = InstalledMappings(self.flags, planning_workspace=self.user)
        installed.register_source(origin.read_text(), origin)
        with self.assertRaisesRegex(ValueError, 'object is absent'):
            installed.source_resolution('Coq.Missing', {'Coq.Missing': str(source)}, origin=origin)

    def test_source_only_duplicate_basenames_keep_ambiguity_refusal(self):
        modules = {}
        for directory in ['first', 'second']:
            source = self.user / directory / 'Values.v'
            source.parent.mkdir()
            source.write_text('Definition value := 0.\n')
            modules['example.' + directory + '.Values'] = str(source)
        origin = self.root / 'Consumer.v'
        origin.write_text('From example Require Import Values.\n')
        installed = InstalledMappings(['-R', str(self.user), 'example'],
            planning_workspace=self.root, source_files=modules)
        installed.register_source(origin.read_text(), origin)
        with self.assertRaisesRegex(ValueError, 'ambiguous'):
            installed.source_resolution('example.Values', modules, origin=origin)

    def test_source_only_contexts_must_agree_without_origin(self):
        sail = self.root / 'sail'
        sail.mkdir()
        first = sail / 'Values.v'
        second = self.user / 'Values.v'
        for source in [first, second]:
            source.write_text('Definition value := 0.\n')
        modules = {'SailStdpp.Values': str(first), 'example.Values': str(second)}
        installed = InstalledMappings(['-R', str(self.user), 'example', '-Q', str(sail), 'SailStdpp'],
            planning_workspace=self.root, source_files=modules)
        for directory in [sail, self.root]:
            origin = directory / 'Consumer.v'
            origin.write_text('Require Import Values.\n')
            installed.register_source(origin.read_text(), origin)
        with self.assertRaisesRegex(ValueError, 'contexts.*ambiguously'):
            installed.source_resolution('Values', modules)

    def test_clean_required_switch_closure_schedules_all_six_sources(self):
        from entry_chain_stage import invalidation
        names = ['BranchGuards', 'ContextCollection', 'MaskNormalizer',
                 'ReturnBundle', 'ReturnWand', 'SwitchDispatch']
        modules = {}
        for name in names:
            module = 'ZesuSsz.Automation.Switches.' + name
            source = self.user / 'Automation/Switches' / (name + '.v')
            source.parent.mkdir(parents=True, exist_ok=True)
            source.write_text('(* Source-only switch fixture. *)\n')
            modules[module] = str(source.relative_to(self.root))
        approved = self.user / 'Automation/Approved.v'
        approved.write_text(''.join('Require Export ZesuSsz.Automation.Switches.' + name + '.\n'
                                    for name in names))
        modules['ZesuSsz.Automation.Approved'] = str(approved.relative_to(self.root))
        target = self.user / 'Consumer.v'
        target.write_text('Require Import ZesuSsz.Automation.Approved.\n')
        modules['ZesuSsz.Consumer'] = str(target.relative_to(self.root))
        installed = InstalledMappings(['-Q', str(self.user), 'ZesuSsz'],
            planning_workspace=self.root, source_files=modules)
        edges = scratch.reconcile_import_closure(['ZesuSsz.Consumer'], [], modules,
                                                 self.root, installed)
        forward = {}
        for row in edges:
            forward.setdefault(row['from'], []).append(row['to'])
        missing = scratch.missing_prerequisite_objects(['ZesuSsz.Consumer'], forward,
                                                       modules, self.root)
        plan = invalidation(edges, missing, ['ZesuSsz.Consumer'])
        switches = {'ZesuSsz.Automation.Switches.' + name for name in names}
        self.assertTrue(switches.issubset(plan['prerequisites']))
        self.assertEqual(set(plan['prerequisites']), switches | {'ZesuSsz.Automation.Approved'})
        self.assertTrue(all(plan['ordered_required'].index(name) <
                            plan['ordered_required'].index('ZesuSsz.Automation.Approved')
                            for name in switches))
        self.assertFalse(list(self.root.rglob('*.vo')))

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
