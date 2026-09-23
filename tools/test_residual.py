"""Tests for the residual corpus tools."""

import shutil
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parent / "residual"))

import capture  # noqa: E402
import classify  # noqa: E402
import goals  # noqa: E402
import label  # noqa: E402
import modules  # noqa: E402
import population  # noqa: E402
import benchmark  # noqa: E402

MODULE = """Require Import ZesuSsz.Automation.All.

Definition helper := 1.

Lemma first_lemma : True.
Proof.
  move => *.
  zesu_block.
Qed.

Lemma inline_lemma : True.
Proof. done. Qed.

Section Block.
Lemma third_lemma : True.
Proof.
  iExists (writeOutputEvents, tt)L.
  bv_solve. Qed.
End Block.

Print Assumptions third_lemma.
"""

SHOW_OUTPUT = """RESIDUAL-BEGIN
2 goals

  sp : bv 64
  ============================
  bv_unsigned sp = 8

goal 2 is:
 "Harray" : base ↦ₘ∗ bytes
 --------------------------------------∗
 find_in_context (FindDirect (λ a, a ↦ₘ v))
RESIDUAL-END
"""


class ParseModule(unittest.TestCase):
    def setUp(self):
        self.directory = tempfile.TemporaryDirectory()
        self.path = Path(self.directory.name) / "Example.v"
        self.path.write_text(MODULE)
        self.proofs = modules.parse_module(self.path)

    def tearDown(self):
        self.directory.cleanup()

    def test_finds_every_proof(self):
        self.assertEqual([proof.name for proof in self.proofs],
                         ["first_lemma", "inline_lemma", "third_lemma"])

    def test_separates_automation_from_hand_lines(self):
        first, inline, third = self.proofs
        self.assertEqual(first.hand_lines, ["move => *."])
        self.assertEqual(inline.hand_lines, ["done."])
        self.assertIn("bv_solve.", third.hand_lines)

    def test_strips_a_terminator_that_shares_a_line(self):
        self.assertNotIn("Qed.", "".join(self.proofs[2].body))

    def test_records_the_open_blocks(self):
        self.assertEqual(self.proofs[2].open_blocks, ["Block"])
        self.assertEqual(self.proofs[0].open_blocks, [])

    def test_probe_keeps_the_statement_and_closes_the_block(self):
        source, hand = capture.probe_text(self.path, "third_lemma")
        self.assertTrue(source.startswith("Set Printing Width 200."))
        self.assertIn("Lemma third_lemma : True.", source)
        self.assertNotIn("bv_solve", source)
        self.assertIn("zesu_block.", source)
        self.assertTrue(source.rstrip().endswith("End Block."))
        self.assertIn("bv_solve.", "".join(hand))

    def test_the_solver_probe_focuses_one_goal(self):
        source, _ = capture.probe_text(self.path, "first_lemma", solver=True)
        self.assertIn("1: first [assert_succeeds (bv_solve)", source)

    def test_the_pure_probe_keeps_the_goal(self):
        source, _ = capture.probe_text(self.path, "first_lemma",
                                       variant="pure")
        self.assertIn("try zesu_block.", source)

    def test_the_standard_probe_is_one_line(self):
        source, _ = capture.probe_text(self.path, "first_lemma")
        self.assertIn('idtac "RESIDUAL-BEGIN". move => *. zesu_block.'
                      " all: liShow. Show.", source)


class CountGoals(unittest.TestCase):
    def test_counts_and_slices_the_show_output(self):
        count, text = capture.count_goals(SHOW_OUTPUT)
        self.assertEqual(count, 2)
        self.assertIn("goal 2 is:", text)
        self.assertNotIn("RESIDUAL-END", text)

    def test_a_closed_proof_reports_no_goals(self):
        self.assertEqual(capture.count_goals(
            "RESIDUAL-BEGIN\nNo more goals.\nRESIDUAL-END\n"), (0, ""))

    def test_missing_markers_report_nothing(self):
        self.assertEqual(capture.count_goals("Error: no such goal"), (0, ""))

    def test_output_without_a_header_still_counts_as_residual(self):
        count, text = capture.count_goals(
            "RESIDUAL-BEGIN\n  x : nat\n  ====\n  x = x\nRESIDUAL-END")
        self.assertEqual(count, 1)
        self.assertIn("x = x", text)

    def test_heads_come_from_below_each_rule(self):
        _, text = capture.count_goals(SHOW_OUTPUT)
        self.assertEqual(capture.goal_heads(text),
                         ["bv_unsigned sp = 8",
                          "find_in_context (FindDirect (λ a, a ↦ₘ v))"])


class SplitGoal(unittest.TestCase):
    def test_the_iris_rule_wins_over_the_coq_rule(self):
        block = goals.split_goals(capture.count_goals(SHOW_OUTPUT)[1])[1]
        context, conclusion = goals.split_goal(block)
        self.assertIn("↦ₘ∗ bytes", context)
        self.assertTrue(conclusion.startswith("find_in_context"))

    def test_head_constant_skips_the_openers(self):
        self.assertEqual(goals.head_constant('⌜bv_unsigned sp = 8⌝'),
                         "bv_unsigned")


class Label(unittest.TestCase):
    def test_an_events_witness_is_class_one(self):
        self.assertEqual(label.label_proof(
            ["iExists (writeOutputEventsAny x y, tt)L."])[0], "L1")

    def test_an_array_lookup_is_class_two(self):
        self.assertEqual(label.label_proof(
            ["iApply find_in_context_mem_mapsto_semantic."])[0], "L2")

    def test_an_events_witness_stays_class_one(self):
        self.assertEqual(label.label_proof(
            ["iExists (writeOutputEvents x, tt)L."])[0], "L1")

    def test_a_sealed_unfold_is_class_three(self):
        self.assertEqual(label.label_proof(
            ['iEval (rewrite bundle_unfold) in "H".'])[0], "L3")

    def test_pure_arithmetic_alone_is_class_four(self):
        self.assertEqual(label.label_proof(["intros.", "bv_solve."])[0], "L4")

    def test_arithmetic_plus_more_is_not_class_four(self):
        self.assertNotIn("L4", label.label_proof(
            ["iDestruct select (_ ∗ _) as \"[A B]\".", "bv_solve."])[1])

    def test_a_payload_is_class_two(self):
        self.assertEqual(label.label_proof(
            ["iApply write_success_payload_at_split."])[0], "L2")

    def test_an_unmatched_proof_is_other(self):
        self.assertEqual(label.label_proof(["iPoseProof foo as \"H\"."])[0],
                         "Lother")


class Classify(unittest.TestCase):
    def predict(self, text):
        return classify.classify(text).pred_class

    def test_a_trace_witness_is_class_one(self):
        self.assertEqual(self.predict(
            "  ============================\n"
            "  ∃ x : spec *ₗ (), ⌜scons (SWriteMem a) snil ⊆ scons_snap x⌝"),
            "C1")

    def test_a_word_wanted_from_an_array_is_class_two(self):
        self.assertEqual(self.predict(
            ' "Harray" : base ↦ₘ∗ bytes\n'
            " --------------------------------------∗\n"
            " find_in_context (FindMemMapsTo a) (λ v, v)"), "C2")

    def test_an_array_slice_is_class_two(self):
        self.assertEqual(self.predict(
            " --------------------------------------∗\n"
            " address ↦ₘ∗ take 18 values"), "C2")

    def test_a_byte_list_witness_is_class_two(self):
        self.assertEqual(self.predict(
            "  ============================\n"
            "  ∃ y : list (bv 8) *ₗ (), True"), "C2")

    def test_an_unfold_equivalence_is_class_three(self):
        self.assertEqual(self.predict(
            "  base : Z\n  ============================\n"
            "  uPred_equiv' (writeSuccessSuffixHashesCallerBundle base)"
            " (base ↦ₘ∗ source)"), "C3")

    def test_a_side_condition_is_class_four(self):
        self.assertEqual(self.predict(
            '  "Hx" : "x1" ↦ᵣ RVal_Bits v\n'
            "  ============================\n"
            "  bv_or (bv_zero_extend 64 v ≪ 8) w = bv_or a b"), "C4")

    def test_a_frame_over_a_folded_context_is_class_six(self):
        self.assertEqual(self.predict(
            " _ : exactTailWithdrawalsBranchZeroEntry args witness P\n"
            " --------------------------------------∗\n"
            ' reg_col zesu_ram_sys_regs ∗ "x2" ↦ᵣ RVal_Bits sp'), "C6")

    def test_a_frame_over_an_atomized_context_is_unknown(self):
        prediction = classify.classify(
            ' _ : "x9" ↦ᵣ RVal_Bits v\n'
            " --------------------------------------∗\n"
            ' reg_col shapes ∗ "x2" ↦ᵣ RVal_Bits sp')
        self.assertEqual(prediction.pred_class, "unknown")
        self.assertIn("atomized", prediction.detail["shape"])

    def test_an_instruction_lookup_is_class_seven(self):
        prediction = classify.classify(
            " _ : writeSuccessCompleteNativeCode\n"
            " --------------------------------------□\n"
            " find_in_context (FindInstrKind 87656 false) (λ ik, True)")
        self.assertEqual(prediction.pred_class, "C7")
        self.assertTrue(prediction.detail["bundle"])

    def test_a_bare_match_is_class_eight(self):
        self.assertEqual(self.predict(
            " --------------------------------------∗\n"
            " match writeSuccessTransactionData t with\n"
            " | [] => True\n | _ :: _ => False\n end -∗ True"), "C8")

    def test_a_closed_probe_has_no_prediction(self):
        self.assertEqual(classify.classify("", "closed").pred_class, "n/a")

    def test_every_goal_gets_a_class(self):
        prediction = classify.classify(capture.count_goals(SHOW_OUTPUT)[1])
        self.assertEqual(prediction.detail["classes"], ["C4", "C2"])


class Population(unittest.TestCase):
    def test_a_trivial_unfold_lemma_is_its_own_population(self):
        self.assertEqual(population.population(
            "Interfaces.v", "bundle_unfold", ["done."]), "unfold")

    def test_a_refused_statement_is_pure(self):
        self.assertEqual(population.population(
            "WriteSuccessThing.v", "helper", ["lia."], "not_bi"), "pure")

    def test_a_model_module_is_pure(self):
        self.assertEqual(population.population(
            "WriteSuccessExactValueModel.v", "value_model", ["done."]), "pure")

    def test_everything_else_is_iris(self):
        self.assertEqual(population.population(
            "WriteSuccessThing.v", "thing_correct", ["iFrame."]), "iris")


class Labels(unittest.TestCase):
    def test_a_code_step_is_label_seven(self):
        self.assertEqual(label.label_proof(["zesu_expose_code_lists."])[0],
                         "L7")

    def test_a_named_unfold_is_label_six(self):
        self.assertEqual(label.label_proof(
            ['iEval (rewrite /writeSuccessTailFrame) in "H".'])[0], "L6")

    def test_plain_glue_is_not_label_six(self):
        self.assertNotIn("L6", label.label_proof(
            ['iEval (rewrite lookup_app) in "H".'])[1])


if __name__ == "__main__":
    unittest.main()


class ImmutableArmTree(unittest.TestCase):
    """Plan 9.1: an arm never reads the working tree.

    The first v2 arm did, and the tree was edited while it ran: every
    probe failed to build and all 305 rows landed in the `n/a` class.
    """

    def setUp(self):
        self.directory = Path(tempfile.mkdtemp())
        self.repository = self.directory / "repo"
        (self.repository / "ZesuSsz" / "Automation").mkdir(parents=True)
        (self.repository / "ZesuSsz" / "Automation" / "Finish.v").write_text(
            "committed\n")
        (self.repository / "generated").mkdir()
        (self.repository / "generated" / "trace.txt").write_text("derived\n")
        for command in (["git", "init", "-q"],
                        ["git", "config", "user.email", "t@example.com"],
                        ["git", "config", "user.name", "t"],
                        ["git", "add", "ZesuSsz"],
                        ["git", "commit", "-q", "-m", "one"]):
            subprocess.run(command, cwd=self.repository, check=True)
        self.commit = subprocess.run(
            ["git", "rev-parse", "HEAD"], cwd=self.repository,
            capture_output=True, text=True, check=True).stdout.strip()

    def tearDown(self):
        shutil.rmtree(self.directory, ignore_errors=True)

    def test_an_edit_after_the_checkout_does_not_reach_the_arm(self):
        tree = benchmark.source_tree(self.repository, self.commit,
                                     self.directory / "arm")
        target = tree / "ZesuSsz" / "Automation" / "Finish.v"
        self.assertEqual(target.read_text(), "committed\n")
        (self.repository / "ZesuSsz" / "Automation" / "Finish.v").write_text(
            "edited while the arm ran\n")
        self.assertEqual(target.read_text(), "committed\n")

    def test_the_derived_inputs_come_along(self):
        tree = benchmark.source_tree(self.repository, self.commit,
                                     self.directory / "arm")
        self.assertEqual((tree / "generated" / "trace.txt").read_text(),
                         "derived\n")

    def test_no_path_reuses_the_working_tree(self):
        self.assertFalse(hasattr(benchmark, "automation_matches"))


class RelativeArmRecipe(unittest.TestCase):
    def test_concurrent_probes_use_the_immutable_tree_cwd(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory) / "arm"
            proof_dir = root / benchmark.PROOF_DIR
            proof_dir.mkdir(parents=True)
            for name in ("First.v", "Second.v"):
                (proof_dir / name).write_text(
                    "Lemma test_lemma : True.\nProof. done. Qed.\n")
            recipe = root / "_build" / "default" / "trace.csexp"
            recipe.parent.mkdir(parents=True)
            recipe.write_text("immutable-tree\n")
            scratch = root / "tools" / "coqc_scratch.sh"
            scratch.parent.mkdir()
            scratch.write_text(
                "#!/bin/sh\n"
                "test \"$(cat _build/default/trace.csexp)\" = immutable-tree || exit 9\n"
                "printf 'RESIDUAL-BEGIN\\nNo more goals.\\nRESIDUAL-END\\n'\n")
            caller_cwd = Path.cwd()
            with patch.object(benchmark, "wait_for_room"):
                rows = benchmark.measure(
                    root, [("First.v", "test_lemma"),
                           ("Second.v", "test_lemma")],
                    jobs=2, seconds=5)
            self.assertEqual([row["outcome"] for row in rows],
                             ["closed", "closed"])
            self.assertEqual(Path.cwd(), caller_cwd)


if __name__ == "__main__":
    unittest.main()
