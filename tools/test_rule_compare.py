"""Check contract preservation, switch isolation, and diagnostic classification."""
import sys
import tempfile
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent / "block"))
import rule_compare

SOURCE = '''Require Import All.
Require Import Approved.
Definition entry := True.
Lemma helper : True.
Proof.
  exact I.
Qed.
Lemma DesignedBoundary_800d6a38 (n : nat) : n = n.
Proof.
  reflexivity.
Qed.
Print Assumptions DesignedBoundary_800d6a38.
'''
GOAL = '''CHAIN-GOAL-BEGIN active
CHAIN-GOAL-ENV coq CHAIN-FIELD-END
CHAIN-GOAL-CONCLUSION (exists n : nat, n = 0) CHAIN-FIELD-END
CHAIN-GOAL-END
'''
RETURNED = 'RULE-COMPARE-BEGIN\nRULE-COMPARE-RETURNED\n'
INCOMPLETE = 'Error: (in proof DesignedBoundary_800d6a38): Attempt to save an incomplete proof\n'
COMPILER = {"limit": None, "policy_error": None, "compiled_object": None}


class GenerationTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.workspace = Path(self.temp.name)
        (self.workspace / "Approved.v").write_text(
            'Require Export Switch.\n')
        (self.workspace / "Switch.v").write_text(
            '#[export] Instance enabled : TestSwitch := I.\n')
        self.module = self.workspace / "Block.v"
        self.module.write_text(SOURCE)

    def prepare(self, **kwargs):
        return rule_compare.prepare(self.module, self.workspace, "TestSwitch", **kwargs)

    def test_preserves_statement_imports_and_helper(self):
        prepared = self.prepare()
        for source in prepared["copies"].values():
            self.assertIn(prepared["statement"], source)
            self.assertEqual(list(rule_compare.imported_modules(source)), ["All", "Approved"])
            self.assertIn('Lemma helper : True.\nProof.\n  exact I.\nQed.', source)
            self.assertIn('  zesu_block.\n', source)
        self.assertEqual(self.module.read_text(), SOURCE)

    def test_canonical_arms_retain_approved_instance_only_in_on(self):
        prepared = self.prepare()
        self.assertEqual(prepared["existing_instances"], ["Switch.enabled"])
        self.assertIn('Remove Hints Switch.enabled : typeclass_instances.', prepared["copies"]["rule_off"])
        self.assertNotIn('Remove Hints', prepared["copies"]["rule_on"])
        self.assertNotIn('#[local] Instance', prepared["copies"]["rule_on"])
        self.assertNotIn('#[local] Instance', prepared["copies"]["rule_off"])
        self.assertIn('Fail Definition rule_compare_switch_probe', prepared["copies"]["rule_off"])
        self.assertNotIn('Fail Definition', prepared["copies"]["rule_on"])
        self.assertEqual(prepared["arm_instances"]["rule_on"],
                         {"removals": [], "local_additions": [], "expected_enabled": True})
        self.assertEqual(prepared["arm_instances"]["rule_off"]["removals"], ["Switch.enabled"])

    def test_future_switch_absent_from_approved_uses_only_local_on_instance(self):
        (self.workspace / "Switch.v").write_text('Class TestSwitch : Prop := constructor : True.\n')
        prepared = self.prepare()
        self.assertEqual(prepared["existing_instances"], [])
        self.assertIn('#[local] Instance : TestSwitch := I.', prepared["copies"]["rule_on"])
        self.assertNotIn('#[local] Instance', prepared["copies"]["rule_off"])
        self.assertEqual(prepared["arm_instances"]["rule_on"]["local_additions"],
                         ['#[local] Instance : TestSwitch := I.'])
        self.assertEqual(prepared["arm_instances"]["rule_off"]["removals"], [])

    def test_finds_all_instances_and_import_cycle(self):
        (self.workspace / "Switch.v").write_text(
            'Require Import Approved.\n'
            '#[export] Instance first : TestSwitch := I.\n'
            '#[export] Instance second : TestSwitch := I.\n')
        prepared = self.prepare()
        self.assertEqual(prepared["existing_instances"], ["Switch.first", "Switch.second"])
        self.assertEqual(prepared["arm_instances"]["rule_off"]["removals"],
                         ["Switch.first", "Switch.second"])
        self.assertEqual(prepared["arm_instances"]["rule_on"]["removals"], [])

    def test_ignores_commented_instances_and_imports(self):
        (self.workspace / "Switch.v").write_text(
            '(* Require Import Missing. (* nested *)\n'
            'Instance fake : TestSwitch := I. *)\n'
            '#[export] Instance enabled : TestSwitch := I.\n')
        self.assertEqual(self.prepare()["existing_instances"], ["Switch.enabled"])

    def test_optional_lemma_is_one_line(self):
        prepared = self.prepare(keyed_lemma="Facts.keyed")
        for source in prepared["copies"].values():
            self.assertEqual(source.count('  apply Facts.keyed.\n'), 1)
        with self.assertRaises(ValueError):
            self.prepare(keyed_lemma="Facts.keyed. admit.")

    def test_missing_or_ambiguous_main_proof_rejects(self):
        with self.assertRaises(ValueError):
            self.prepare(lemma="absent")
        self.module.write_text(SOURCE + 'Lemma DesignedBoundary_other : True.\nProof.\nexact I.\nQed.\n')
        with self.assertRaises(ValueError):
            self.prepare()

    def test_aborted_source_rejects(self):
        self.module.write_text(SOURCE.replace('  reflexivity.\nQed.', '  reflexivity.\nAbort.'))
        with self.assertRaises(ValueError):
            self.prepare()

    def test_records_shelf_targets_after_unshelve(self):
        for source in self.prepare()["copies"].values():
            self.assertIn('  Unshelve.\n  all: idtac "RULE-COMPARE-RETURNED".', source)
            self.assertIn('chain_print_goal "shelved"', source)


class ClassificationTests(unittest.TestCase):
    def test_incomplete_proof_with_complete_goal_is_residual(self):
        result = rule_compare.classify(1, RETURNED + GOAL + INCOMPLETE, COMPILER)
        self.assertEqual(result["outcome"], "residual:existential")
        self.assertEqual(result["first_residual"]["conclusion"], '(exists n : nat, n = 0)')

    def test_missing_import_is_setup_error(self):
        result = rule_compare.classify(1, 'Error: Cannot find a physical path bound to All.', COMPILER)
        self.assertEqual(result["outcome"], "setup-error")
        self.assertIsNone(result["first_residual"])

    def test_missing_recipe_is_setup_error(self):
        self.assertEqual(rule_compare.classify(2, 'no compiler recipe', None)["outcome"], "setup-error")

    def test_arbitrary_compiler_error_is_not_residual(self):
        result = rule_compare.classify(1, RETURNED + GOAL + 'Error: unknown reference.', COMPILER)
        self.assertEqual(result["outcome"], "compiler-error")
        self.assertIsNone(result["first_residual"])

    def test_tactic_failure_is_not_residual(self):
        result = rule_compare.classify(1, 'RULE-COMPARE-BEGIN\nError: Tactic failure.', COMPILER)
        self.assertEqual(result["outcome"], "tactic-error")

    def test_truncated_capture_is_not_residual(self):
        result = rule_compare.classify(1, RETURNED + 'CHAIN-GOAL-BEGIN active\n' + INCOMPLETE, COMPILER)
        self.assertEqual(result["outcome"], "capture-error")

    def test_resource_stop_is_not_residual(self):
        result = rule_compare.classify(1, RETURNED + GOAL + INCOMPLETE, {**COMPILER, "limit": "memory"})
        self.assertEqual(result["outcome"], "runtime-error")

    def test_shelf_only_residual_uses_complete_post_unshelve_target(self):
        shelf = GOAL.replace('CHAIN-GOAL-BEGIN active', 'CHAIN-GOAL-BEGIN shelved')
        result = rule_compare.classify(1, RETURNED + shelf + INCOMPLETE, COMPILER)
        self.assertEqual(result["outcome"], "residual:existential")
        self.assertEqual(result["first_residual"]["phase"], "post-unshelve")
        self.assertEqual(result["first_residual"]["conclusion"], '(exists n : nat, n = 0)')

    def test_legacy_shelf_only_record_marks_targets_unavailable(self):
        output = ('RULE-COMPARE-BEGIN\nExistential 1 = ?pending\n'
                  'Chars 100 - 118 [Show~Existentials.] 0. secs\n' + INCOMPLETE)
        result = rule_compare.classify(1, output, COMPILER)
        self.assertEqual(result["outcome"], "residual:shelved-unavailable")
        self.assertIsNone(result["first_residual"]["conclusion"])

    def test_other_theorem_qed_failure_is_not_target_residual(self):
        result = rule_compare.classify(1, RETURNED + GOAL + INCOMPLETE,
                                       COMPILER, lemma="another_theorem")
        self.assertEqual(result["outcome"], "compiler-error")

    def test_closure_requires_object_and_empty_assumptions(self):
        closed = {**COMPILER, "compiled_object": {"path": "candidate.vo"}}
        self.assertEqual(rule_compare.classify(0, 'RULE-COMPARE-BEGIN\nClosed under the global context', closed)["outcome"], "closed")
        result = rule_compare.classify(0, RETURNED + 'Axioms:\nfixture : False', closed)
        self.assertEqual(result["outcome"], "compiler-error")


if __name__ == "__main__":
    unittest.main()
