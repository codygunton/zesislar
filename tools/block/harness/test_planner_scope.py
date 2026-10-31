"""Exercise the actual preparation planner without admission or proof work."""
import ast
import inspect
from pathlib import Path
from types import SimpleNamespace
import tempfile
import unittest

import scratch
from entry_chain_stage import import_commands


class PlannerScopeTests(unittest.TestCase):
    def setUp(self):
        self.directory = tempfile.TemporaryDirectory()
        self.addCleanup(self.directory.cleanup)
        self.workspace = Path(self.directory.name)
        self.rules = scratch.RULES
        self.generated = 'Example.Generated.Entry'
        self.sources = {
            'First': 'Require Import Shared ' + self.rules + '.\n',
            'Second': 'Require Import SecondOwner.\n',
            self.generated: 'Require Import GeneratedOwner.\n',
            self.rules: 'Require Import Shared.\n',
            'Shared': '', 'SecondOwner': '', 'GeneratedOwner': '',
        }
        self.modules = {name: name.replace('.', '_') + '.v' for name in self.sources}
        for name, text in self.sources.items():
            source = self.workspace / self.modules[name]
            source.write_text(text)
            if name != 'First':
                # These bytes are unit data, never compiler or admission evidence.
                source.with_suffix('.vo').write_bytes(b'unit object')
        self.edges = [{'from': 'First', 'to': 'Shared'},
                      {'from': 'First', 'to': self.rules},
                      {'from': self.rules, 'to': 'Shared'}]

    def plan(self, changed=(), *, declarations=True):
        # Execute the planning block from prepare(). This includes its actual
        # scope selection and filtering, rather than duplicating those branches.
        body = ast.parse(inspect.getsource(scratch.prepare)).body[0].body
        start = next(i for i, node in enumerate(body)
                     if isinstance(node, ast.Assign)
                     and any(isinstance(target, ast.Name) and target.id == 'plan_targets'
                             for target in node.targets))
        end = next(i for i, node in enumerate(body[start:], start)
                   if isinstance(node, ast.Assign)
                   and any(isinstance(target, ast.Subscript)
                           and isinstance(target.value, ast.Name) and target.value.id == 'plan'
                           and isinstance(target.slice, ast.Constant) and target.slice.value == 'proof_ran'
                           for target in node.targets))
        code = compile(ast.Module(body=body[start:end + 1], type_ignores=[]),
                       str(Path(scratch.__file__)), 'exec')

        class Resolver:
            def register_source(self, *args):
                pass

            def resolve(self, name):
                raise ValueError('The unit fixture has no installed owner: ' + name)

        namespace = dict(vars(scratch),
            a=SimpleNamespace(prerequisite_target_union=False,
                              declarations_only=declarations,
                              rules=Path('Rules.v') if declarations else None,
                              control_session=declarations),
            targets=[{'module': 'First'}, {'module': 'Second'}], module='First',
            edges=list(self.edges), modules=self.modules, workspace=self.workspace,
            installed=Resolver(), changed=list(changed))
        exec(code, namespace)
        return namespace['plan']

    def test_compatible_control_has_no_compiles(self):
        plan = self.plan([self.rules])
        self.assertEqual(plan['ordered_required'], [self.rules])
        self.assertEqual(plan['prerequisites'], [])
        self.assertNotIn('First', plan['ordered_required'])
        self.assertNotIn(self.generated, plan['ordered_required'])

    def test_selected_native_body_is_excluded_from_setup(self):
        plan = self.plan(['First'], declarations=False)
        self.assertEqual(plan['ordered_required'], ['First'])
        self.assertEqual(plan['native_targets'], ['First'])
        self.assertEqual(plan['prerequisites'], [])

    def test_changed_required_dependency_is_compiled(self):
        plan = self.plan(['Shared', 'GeneratedOwner'])
        self.assertEqual(plan['prerequisites'], ['Shared'])
        self.assertEqual(plan['ordered_required'], ['Shared', self.rules])
        self.assertNotIn('GeneratedOwner', plan['ordered_required'])

    def test_unchanged_generated_header_still_repairs_import_coverage(self):
        plan = self.plan()
        edges = {(row['from'], row['to']) for row in plan['import_edges']}
        self.assertIn((self.generated, 'GeneratedOwner'), edges)
        self.assertIn(('Second', 'SecondOwner'), edges)
        self.assertEqual(plan['prerequisites'], [])

    def test_missing_generated_source_still_refuses(self):
        (self.workspace / self.modules['GeneratedOwner']).unlink()
        with self.assertRaisesRegex(ValueError, 'closure source is absent'):
            self.plan()

    def test_unselected_target_import_still_refuses_unknown_owner(self):
        (self.workspace / self.modules['Second']).write_text('Require Import UnknownOwner.\n')
        with self.assertRaisesRegex(ValueError, 'no installed owner: UnknownOwner'):
            self.plan()


class ImportCommandTests(unittest.TestCase):
    def test_exact_parenthesized_modifier_is_not_a_library(self):
        commands = import_commands('From Coq.ssr Require Import (notations) ssrfun.')
        self.assertEqual(commands[0][1], ['Coq.ssr.ssrfun'])
        self.assertEqual(commands[0][0],
                         ['From', 'Coq.ssr', 'Require', 'Import', '(', 'notations', ')', 'ssrfun'])

    def test_ordinary_imports_keep_all_library_names(self):
        commands = import_commands('Require Import Example.First Example.Second.\n'
                                   'From Example Require Export Third.\nImport LocalNames.')
        self.assertEqual([names for _, names in commands],
                         [['Example.First', 'Example.Second'], ['Example.Third'], ['LocalNames']])

    def test_incomplete_modifier_refuses(self):
        with self.assertRaises(ValueError):
            import_commands('From Coq.ssr Require Import (notations ssrfun.')


if __name__ == '__main__':
    unittest.main()
