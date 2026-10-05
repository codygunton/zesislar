"""Source declarations constrain binder order and argument arity."""
from pathlib import Path
import sys
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

    def test_bound_source_and_ordered_json_binders_must_match(self):
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
            block['binders'].reverse()
            with self.assertRaisesRegex(ValueError, 'binders do not match'):
                check_binders(block, root)
            block['binders'].reverse()
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


if __name__ == '__main__':
    unittest.main()
