"""Source declarations constrain binder order and argument arity."""
from pathlib import Path
import sys
import json
import hashlib
import tempfile
import unittest
sys.path.insert(0, str(Path(__file__).resolve().parent / 'block'))
from entry_bindings import declared_binders, normalize_type, check_binders, application_source


class EntryBindingTests(unittest.TestCase):
    def test_grouped_binders_expand_in_declared_order(self):
        source = 'Definition entry `{!islaG Sigma} `{!threadG} (args : Args) (n cursor : Z) : iProp Sigma := True.'
        self.assertEqual(declared_binders(source, 'entry'), [
            {'name': 'args', 'type': 'Args'}, {'name': 'n', 'type': 'Z'}, {'name': 'cursor', 'type': 'Z'}])

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


if __name__ == '__main__':
    unittest.main()
