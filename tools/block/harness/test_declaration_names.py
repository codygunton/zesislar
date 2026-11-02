"""Check bounded Ltac visibility without importing or executing Rocq."""
import json
from pathlib import Path
import tempfile
import unittest

from declaration_names import check, document, inspect
from entry_chain import binding, save


class DeclarationNamesTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)

    def docs(self, sources):
        result = {}
        for module, text in sources.items():
            source = self.root / (module + '.v')
            source.write_text(text)
            result[module] = document(module, source)
        return result

    def report(self, text, helper='Ltac project_switch x := idtac.\n', extra=None):
        sources = {'Project.Switch': helper, 'Project.Control': text}
        sources.update(extra or {})
        return inspect(['Project.Control'], self.docs(sources))

    def test_missing_import_is_definite_in_complete_visibility(self):
        result = self.report('Goal True. Proof. project_switch constr:(True). Abort.')
        self.assertEqual([x['name'] for x in result['missing']], ['project_switch'])
        self.assertFalse(result['complete_semantic_resolution'])

    def test_import_opens_the_project_tactic(self):
        result = self.report('Require Import Project.Switch. Goal True. Proof. project_switch constr:(True). Abort.')
        self.assertEqual(result['missing'], [])
        self.assertTrue(result['modules'][0]['calls'][0]['project_visibility'])

    def test_require_alone_keeps_bare_name_closed(self):
        result = self.report('Require Project.Switch. Goal True. Proof. project_switch constr:(True). Abort.')
        self.assertEqual(len(result['missing']), 1)

    def test_qualified_name_needs_loaded_module(self):
        for name in ['Project.Switch.project_switch', 'Switch.project_switch']:
            with self.subTest(name=name):
                result = self.report('Require Project.Switch. Goal True. Proof. ' + name + ' constr:(True). Abort.')
                self.assertEqual(result['missing'], [])
                self.assertEqual(result['modules'][0]['calls'][0]['status'], 'visible')
        result = self.report('Goal True. Proof. Project.Switch.project_switch constr:(True). Abort.')
        self.assertEqual(len(result['missing']), 1)

    def test_require_export_is_transitive_but_require_import_is_not(self):
        for mode, expected in [('Export', 'visible'), ('Import', 'missing')]:
            with self.subTest(mode=mode):
                result = self.report('Require Import Project.Umbrella. Goal True. Proof. project_switch constr:(True). Abort.',
                    extra={'Project.Umbrella': 'Require ' + mode + ' Project.Switch.'})
                self.assertEqual(result['modules'][0]['calls'][0]['status'], expected)

    def test_sentence_order_prevents_later_import_authority(self):
        result = self.report('Goal True. Proof. project_switch constr:(True). Abort. Require Import Project.Switch.')
        self.assertEqual(len(result['missing']), 1)

    def test_local_definition_and_recursive_definition_resolve(self):
        result = self.report('Ltac project_switch x := project_switch x. Goal True. Proof. project_switch constr:(True). Abort.')
        self.assertEqual(result['missing'], [])
        self.assertEqual({x['status'] for x in result['modules'][0]['calls']}, {'visible'})

    def test_local_definition_does_not_export(self):
        result = self.report('Require Import Project.Switch. Goal True. Proof. project_switch constr:(True). Abort.',
                             helper='Local Ltac project_switch x := idtac.')
        self.assertEqual(len(result['missing']), 1)

    def test_local_value_binding_reports_unknown(self):
        result = self.report('Goal True. Proof. let project_switch := constr:(True) in project_switch. Abort.')
        self.assertEqual(result['missing'], [])
        self.assertEqual(result['modules'][0]['calls'][0]['status'], 'unknown')

    def test_term_quotations_comments_and_strings_are_not_calls(self):
        result = self.report('(* project_switch *) Goal True. Proof. idtac "project_switch"; let t := constr:(project_switch) in idtac. Abort.')
        self.assertEqual(result['modules'][0]['calls'], [])

    def test_term_name_is_not_a_tactic_call_head(self):
        result = self.report('Lemma local_term (project_switch : True) : True. Proof. exact project_switch. Qed.')
        self.assertEqual(result['modules'][0]['calls'], [])

    def test_nested_definition_does_not_leak_after_end(self):
        result = self.report('Module Inner. Ltac project_switch x := idtac. End Inner. '
                             'Goal True. Proof. project_switch constr:(True). Abort.')
        self.assertEqual(len(result['missing']), 1)

    def test_redefinition_makes_visibility_unknown(self):
        result = self.report('Ltac unknown ::= idtac. Goal True. Proof. project_switch constr:(True). Abort.')
        self.assertEqual(result['missing'], [])
        self.assertEqual(result['modules'][0]['calls'][0]['status'], 'unknown')

    def test_qualified_current_module_cannot_use_a_later_definition(self):
        result = self.report('Goal True. Proof. Project.Control.project_switch constr:(True). Abort. '
                             'Ltac project_switch x := idtac.')
        self.assertEqual(len(result['missing']), 1)
        self.assertEqual(result['missing'][0]['name'], 'Project.Control.project_switch')

    def test_parenthesized_term_binder_is_unknown_not_missing(self):
        result = self.report('Require Project.Switch. Lemma example (project_switch : True) : True. '
                             'Proof. exact (project_switch). Qed.')
        self.assertEqual(result['missing'], [])
        call = result['modules'][0]['calls'][0]
        self.assertEqual(call['status'], 'unknown')
        self.assertIn('ambiguous_parenthesized_reference', call['unknown_reasons'])

    def test_parenthesized_grammar_alone_is_unknown(self):
        result = self.report('Require Project.Switch. Goal True. Proof. exact (project_switch). Abort.')
        self.assertEqual(result['missing'], [])
        self.assertEqual(result['modules'][0]['calls'][0]['status'], 'unknown')

    def test_local_term_binder_does_not_become_a_missing_tactic(self):
        result = self.report('Lemma local_term (project_switch : True) : True. Proof. project_switch. Abort.')
        self.assertEqual(result['missing'], [])
        self.assertEqual(result['modules'][0]['calls'][0]['status'], 'unknown')

    def test_ambiguous_project_name_is_unknown(self):
        result = self.report('Require Import Project.Switch Project.Other. Goal True. Proof. project_switch constr:(True). Abort.',
                             extra={'Project.Other':'Ltac project_switch x := idtac.'})
        self.assertEqual(result['missing'], [])
        self.assertIn('ambiguous_project_name', result['modules'][0]['calls'][0]['unknown_reasons'])

    def test_plugin_makes_missing_visibility_unknown(self):
        result = self.report('Require Import Project.Plugin. Goal True. Proof. project_switch constr:(True). Abort.',
                             extra={'Project.Plugin': 'Declare ML Module "bound-plugin".'})
        call = result['modules'][0]['calls'][0]
        self.assertFalse(call['project_visibility'])
        self.assertEqual(call['status'], 'unknown')
        self.assertIn('unsupported_imported_mechanism:Project.Plugin', call['unknown_reasons'])
        self.assertEqual(result['missing'], [])

    def test_v34_combined_control_reports_unexported_switch_with_plugin_uncertainty(self):
        sources = {
            'Project.Switch': 'Ltac project_switch x := idtac.',
            'Project.Plugin': 'Declare ML Module "signature-gates.plugin".',
            'Project.Hooks': 'Require Import Project.Switch Project.Plugin.',
            'Project.All': 'Require Export Project.Hooks.',
            'Project.Control': 'Require Import Project.All. Goal True. Proof. '
                               'let switches := constr:(True) in '
                               'ltac:(fun _ => project_switch constr:(True)). Abort.'}
        result = inspect(['Project.Control'], self.docs(sources))
        call = result['modules'][0]['calls'][0]
        self.assertEqual(call['name'], 'project_switch')
        self.assertFalse(call['project_visibility'])
        self.assertEqual(call['status'], 'unknown')
        self.assertEqual(result['missing'], [])

    def test_unmodeled_import_and_notation_report_without_refusal(self):
        for command in ['Require Import External.Unknown.', 'Tactic Notation "custom" := idtac.',
                        'Module Alias := External.Unknown.', 'Load "generated.v".']:
            with self.subTest(command=command):
                result = self.report(command + ' Goal True. Proof. project_switch constr:(True). Abort.')
                self.assertEqual(result['missing'], [])
                self.assertEqual(result['modules'][0]['calls'][0]['status'], 'unknown')

    def test_module_scope_qualified_definition(self):
        result = self.report('Require Project.Switch. Goal True. Proof. Project.Switch.Inner.project_switch constr:(True). Abort.',
                             helper='Module Inner. Ltac project_switch x := idtac. End Inner.')
        self.assertEqual(result['missing'], [])

    def test_all_planned_modules_report_before_first_refusal(self):
        docs = self.docs({'Project.Switch': 'Ltac project_switch x := idtac.',
                          'Project.First': 'Goal True. Proof. project_switch constr:(True). Abort.',
                          'Project.Second': 'Goal True. Proof. project_switch constr:(False). Abort.'})
        result = inspect(['Project.First', 'Project.Second'], docs)
        self.assertEqual(len(result['missing']), 2)

    def test_runtime_check_publishes_before_refusal_without_compilation(self):
        docs = self.docs({'Project.Switch': 'Ltac project_switch x := idtac.',
                          'Project.Control': 'Require Project.Switch. Goal True. Proof. project_switch constr:(True). Abort.'})
        graph = self.root / 'GRAPH.json'
        save(graph, {'import_edges': [{'from': 'Project.Control', 'to': 'Project.Switch'}]})
        runtime = {'ordered_modules': ['Project.Control'], 'cache_import_graph': binding(graph),
                   'module_files': {n: Path(d['source']['path']).name for n, d in docs.items()}}
        with self.assertRaisesRegex(ValueError, 'lacks a visible definition'):
            check(runtime, self.root, self.root)
        result = json.loads((self.root / 'DECLARATION-NAME-PREFLIGHT.json').read_text())
        self.assertEqual(result['missing'][0]['name'], 'project_switch')
        self.assertEqual(len(result['catalog_sources']), 2)
        self.assertEqual(list(self.root.glob('*.vo')), [])


if __name__ == '__main__':
    unittest.main()
