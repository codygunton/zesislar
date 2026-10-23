"""Source declarations constrain binder order and argument arity."""
from pathlib import Path
from copy import deepcopy
from types import SimpleNamespace
import sys
import json
import hashlib
import tempfile
import unittest
from unittest.mock import patch
sys.path.insert(0, str(Path(__file__).resolve().parent / 'block'))
from entry_bindings import (declared_binders, normalize_type, check_binders,
                            application_source, rendered_entry_views, validate_design)


class EntryBindingTests(unittest.TestCase):
    def test_grouped_binders_expand_in_declared_order(self):
        source = 'Definition entry `{!islaG Sigma} `{!threadG} (args : Args) (n cursor : Z) : iProp Sigma := True.'
        self.assertEqual(declared_binders(source, 'entry'), [
            {'name': 'args', 'type': 'Args'}, {'name': 'n', 'type': 'Z'}, {'name': 'cursor', 'type': 'Z'}])

    def test_numeric_token_boundaries_remain_distinct(self):
        self.assertEqual(normalize_type('bv 64'), 'bv 64')
        self.assertEqual(normalize_type('bv 6 4'), 'bv 6 4')
        self.assertNotEqual(normalize_type('bv 64'), normalize_type('bv 6 4'))
        declared = declared_binders(
            'Definition entry (value : bv 64) : Type := nat.', 'entry')
        self.assertEqual(declared, [{'name': 'value', 'type': 'bv 64'}])
        self.assertNotEqual(declared[0]['type'], normalize_type('bv 6 4'))

    def test_comments_cannot_supply_a_missing_definition(self):
        with self.assertRaisesRegex(ValueError, 'unambiguous'):
            declared_binders('(* Definition entry (args : Args) : Type := nat. *)', 'entry')

    def test_nested_type_parentheses_are_retained(self):
        result = declared_binders('Definition entry (f : (Z -> Z) -> Prop) : Type := nat.', 'entry')
        self.assertEqual(result[0]['type'], normalize_type('(Z -> Z) -> Prop'))

    def test_implicit_locals_are_not_silently_discarded(self):
        with self.assertRaisesRegex(ValueError, 'implicit binder'):
            declared_binders('Definition entry {args : Args} : Prop := True.', 'entry')

    def test_application_locals_do_not_replace_source_signature(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            source = root/'Fixture.v'
            source.write_text('Definition entry (domain : Args -> Prop) (args : Args) : iProp Sigma := True.')
            block = {'entry_definition': 'Fixture.entry', 'resource_predicate': 'Fixture.entry',
                     'binders': [{'name': 'domain', 'type': 'Args -> Prop'}, {'name': 'args', 'type': 'Args'}],
                     'arguments': ['constantDomain', 'args'],
                     'source_hashes': {'Fixture.v': hashlib.sha256(source.read_bytes()).hexdigest()}}
            check_binders(block, root)
            self.assertEqual(block['arguments'], ['constantDomain', 'args'])
            block['binders'] = [{'name': 'returnAddress', 'type': 'Z'},
                                {'name': 'args', 'type': 'Args'}]
            declared = check_binders(block, root)
            self.assertEqual(declared[0], {'name': 'domain', 'type': normalize_type('Args -> Prop')})
            self.assertEqual(block['binders'][0]['name'], 'returnAddress')
            block['arguments'].pop()
            with self.assertRaisesRegex(ValueError, 'argument count'):
                check_binders(block, root)
            source.write_text('changed')
            with self.assertRaisesRegex(ValueError, 'source hash changed'):
                check_binders(block, root)

    def test_type_queries_preserve_ordered_constant_expressions(self):
        row = {'entry_definition': 'Fixture.entry', 'resource_predicate': 'Fixture.entry',
               'binders': [{'name': 'domain', 'type': 'Args -> Prop'}, {'name': 'args', 'type': 'Args'}],
               'arguments': ['constantDomain', 'args'], 'source_hashes': {'Fixture.v': '0'*64}}
        source = application_source({'blocks': [row]})
        self.assertIn('Require Import isla.riscv64.riscv64.', source)
        self.assertIn('Context (domain : Args -> Prop).', source)
        self.assertIn('Check (Fixture.entry (constantDomain) (args) : iProp Sigma).', source)
        self.assertEqual(source.count('Check ('), 1)
        self.assertNotIn('Proof.', source)
        self.assertNotIn('Axiom', source)

    def test_missing_five_field_schema_is_rejected(self):
        with self.assertRaisesRegex(ValueError, 'five executable entry fields'):
            check_binders({'entry_pc': '0x10'}, '.')

    def test_duplicate_names_in_different_modules_need_a_namespace_check(self):
        with self.assertRaisesRegex(ValueError, 'unambiguous'):
            declared_binders('Module A. Definition entry := True. End A. Module B. Definition entry := True. End B.', 'entry')


class SharedTypeImportTests(unittest.TestCase):
    def test_other23_rows_import_shared_argument_type_directly(self):
        root = Path(__file__).resolve().parents[1]
        design = json.loads((root/'ZesuSsz/Evidence/decode_item_block_design.json').read_text())
        design['blocks'] = [row for row in design['blocks'] if row['entry_pc'] != '0x800d6960']
        self.assertEqual(len(design['blocks']), 23)
        source = application_source(design)
        shared = 'Require Import ZesuSsz.Contracts.RlpDecodeItemContract.'
        self.assertEqual(source.count(shared), 1)
        self.assertLess(source.index(shared), source.index('Context (args : DecodeItemArgs).'))


class RenderedEntryViewTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        old = self.root/'Handwritten.v'
        old.write_text('Definition retained := 0.\n')
        self.old_hash = hashlib.sha256(old.read_bytes()).hexdigest()
        self.output = self.root/'ZesuSsz/Generated/DecodeItem/Entries.v'
        self.output.parent.mkdir(parents=True)
        names = ['Entry698cLiteral', 'Entry698cShortString', 'Entry698c',
                 'Entry6a24', 'Body6a24', 'Entry6ac4', 'Body6ac4']
        self.output.write_text('\n'.join(
            f'Definition {name} (n i : Z) : iProp Sigma := True.' for name in names))
        self.rendered_source = self.output.read_text()
        output_hash = hashlib.sha256(self.output.read_bytes()).hexdigest()
        self.originals = []
        for name in names:
            row = dict(entry_definition='Handwritten.'+name, resource_predicate='Handwritten.'+name,
                       binders=[dict(name='n', type='Z'), dict(name='i', type='Z')],
                       arguments=['n', 'i'], source_hashes={'Handwritten.v': self.old_hash},
                       support=dict(order='pure-first' if name.startswith('Body') else 'resources-first',
                                    tags=['count', 'index']))
            self.originals.append(row)
        self.design = dict(blocks=[self.originals[i] for i in (2, 3, 5)])
        for row, pc in zip(self.design['blocks'], ['0x698c', '0x6a24', '0x6ac4']):
            row['entry_pc'] = pc
        self.design['blocks'][0]['incoming_edges'] = [
            dict(from_block='0x697c', resource_alternative='Handwritten.Entry698cLiteral'),
            dict(from_block='0x69e8', resource_alternative='Handwritten.Entry698cShortString')]
        self.fresh = deepcopy(self.originals)
        for row in self.fresh:
            name = 'ZesuSsz.Generated.DecodeItem.Entries.'+row['entry_definition'].rsplit('.', 1)[-1]
            row.update(entry_definition=name, resource_predicate=name,
                       source_hashes={'ZesuSsz/Generated/DecodeItem/Entries.v': output_hash})
        producer = SimpleNamespace(verify_rendered_entries=lambda *a, **kw: deepcopy(self.fresh))
        renderer = SimpleNamespace(support_declarations=lambda design: deepcopy(self.originals),
            render_support=lambda *a, **kw: {
                Path('ZesuSsz/Generated/DecodeItem/Entries.v'): self.rendered_source})
        self.patch = patch('entry_bindings._rendered_producer', return_value=(producer, renderer))
        self.patch.start()
        self.addCleanup(self.patch.stop)

    def test_primary_and_auxiliary_views_preserve_order_and_inputs(self):
        before = deepcopy(self.design)
        views = rendered_entry_views(self.design, self.root)
        self.assertEqual(self.design, before)
        self.assertEqual(views['primary_count'], 3)
        self.assertEqual(views['auxiliary_count'], 4)
        self.assertEqual(len(views['table_design']['blocks']), 3)
        self.assertEqual(len(views['application_design']['blocks']), 7)
        edges = views['table_design']['blocks'][0]['incoming_edges']
        self.assertEqual([e['resource_alternative'].rsplit('.', 1)[-1] for e in edges],
                         ['Entry698cLiteral', 'Entry698cShortString'])
        rows = views['application_design']['blocks']
        self.assertEqual([r['entry_definition'].rsplit('.', 1)[-1] for r in rows],
                         [r['entry_definition'].rsplit('.', 1)[-1] for r in self.originals])
        self.assertEqual(rows[3]['support']['order'], 'resources-first')
        self.assertEqual(rows[4]['support']['order'], 'pure-first')
        self.assertEqual(rows[4]['support']['tags'], ['count', 'index'])
        self.assertEqual(views['input_source_hashes'], {'Handwritten.v': self.old_hash})
        self.assertEqual(set(views['output_source_hashes']), {'ZesuSsz/Generated/DecodeItem/Entries.v'})
        self.assertEqual(application_source(views['application_design']).count('Check ('), 7)

    def test_missing_and_unused_bindings_are_rejected(self):
        for fresh in (self.fresh[:-1], self.fresh+[self.fresh[0]]):
            with self.subTest(count=len(fresh)):
                saved, self.fresh = self.fresh, fresh
                with self.assertRaisesRegex(ValueError, 'missing or unused'):
                    rendered_entry_views(self.design, self.root)
                self.fresh = saved

    def test_full_inventory_keeps_24_primary_and_four_auxiliary_bindings(self):
        for index in range(21):
            row = deepcopy(self.originals[3])
            row.update(entry_definition=f'Handwritten.Extra{index}',
                       resource_predicate=f'Handwritten.Extra{index}',
                       entry_pc=hex(0x7000+4*index))
            self.originals.append(row)
            self.design['blocks'].append(row)
            fresh = deepcopy(row)
            fresh.update(entry_definition=f'ZesuSsz.Generated.DecodeItem.Entries.Extra{index}',
                         resource_predicate=f'ZesuSsz.Generated.DecodeItem.Entries.Extra{index}')
            self.fresh.append(fresh)
            self.rendered_source += f'\nDefinition Extra{index} (n i : Z) : iProp Sigma := True.'
        self.output.write_text(self.rendered_source)
        sha = hashlib.sha256(self.output.read_bytes()).hexdigest()
        for row in self.fresh:
            row['source_hashes'] = {'ZesuSsz/Generated/DecodeItem/Entries.v': sha}
        views = rendered_entry_views(self.design, self.root)
        self.assertEqual(len(views['table_design']['blocks']), 24)
        self.assertEqual(len(views['application_design']['blocks']), 28)
        self.assertEqual((views['primary_count'], views['auxiliary_count']), (24, 4))

    def test_changed_arguments_metadata_names_and_order_are_rejected(self):
        for mutate in (lambda r: r['arguments'].reverse(),
                       lambda r: r['support'].update(tags=['changed']),
                       lambda r: r.update(entry_definition='Wrong.entry'),
                       lambda r: r.update(extra='unused')):
            with self.subTest(mutate=mutate):
                saved = deepcopy(self.fresh)
                mutate(self.fresh[0])
                with self.assertRaisesRegex(ValueError, 'differs from its ordered input'):
                    rendered_entry_views(self.design, self.root)
                self.fresh = saved
        self.fresh.reverse()
        with self.assertRaisesRegex(ValueError, 'differs from its ordered input'):
            rendered_entry_views(self.design, self.root)

    def test_duplicate_declarations_are_rejected(self):
        self.originals.append(deepcopy(self.originals[0]))
        self.fresh.append(deepcopy(self.fresh[0]))
        with self.assertRaisesRegex(ValueError, 'duplicate bindings'):
            rendered_entry_views(self.design, self.root)

    def test_unmapped_resource_alternative_is_rejected(self):
        self.design['blocks'][0]['incoming_edges'][0]['resource_alternative'] = 'Handwritten.Unknown'
        # The producer copies incoming edges, so retain that condition in its result.
        self.fresh[2]['incoming_edges'] = deepcopy(self.design['blocks'][0]['incoming_edges'])
        with self.assertRaisesRegex(ValueError, 'resource alternative has no rendered binding'):
            rendered_entry_views(self.design, self.root)

    def test_stale_generated_source_is_rejected(self):
        self.output.write_text(self.output.read_text()+'\n')
        with self.assertRaisesRegex(ValueError, 'output is stale'):
            rendered_entry_views(self.design, self.root)

    def test_auxiliary_errors_keep_the_declaration_name(self):
        row = deepcopy(self.fresh[0])
        row['arguments'].pop()
        with self.assertRaisesRegex(ValueError, 'Entry698cLiteral.*argument count'):
            validate_design(dict(blocks=[row]), self.root)


if __name__ == '__main__':
    unittest.main()
