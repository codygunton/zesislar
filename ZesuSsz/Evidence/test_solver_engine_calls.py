"""Solver engines run only through BoundedSolve in Automation2 tactics."""
import unittest
from pathlib import Path

from solver_engine_calls import allowlist, solver_engine_failures

ROOT = Path(__file__).resolve().parents[2]

CORE = "ZesuSsz/Automation2/A.v"


class SolverEngineCalls(unittest.TestCase):
    def test_engines_in_tactic_definitions_fail(self):
        for body in ["Zify.zify; xlia Lia.zchecker", "bv_saturate_unsigned; lia", "nia",
                     "vm_compute; reflexivity", "bv_simplify_arith; bv_solve",
                     "LinearFirstLia.zesu_lia_linear_first3",
                     "ZesuSsz.Automation.PureFacts.zesu_saturate_derived_facts",
                     "eauto 2 with nocore db", "auto with *", "eauto", "solve [info_eauto]"]:
            for source in [f"Ltac t := {body}.", f"Local Ltac t x := {body}.",
                           f"#[export] Hint Extern 1 (P _) => {body} : typeclass_instances.",
                           f'Tactic Notation "t" := {body}.']:
                with self.subTest(source=source):
                    self.assertTrue(solver_engine_failures(CORE, source, {}))

    def test_entry_points_term_evaluation_and_proofs_pass(self):
        for source in ["Ltac t := lia.", "Ltac t := bv_solve.", "Ltac t := Lia.lia.",
                       "Ltac t := typeclasses eauto.",
                       "Ltac t := zesu_bounded_search ltac:(zesu_residual_search).",
                       "Ltac t := BoundedSolve.zesu_bounded_search ltac:(eauto).",
                       "Ltac t := zesu_vm_compute_goal; reflexivity.",
                       "Ltac t x := let v := eval vm_compute in x in exact v.",
                       "Lemma l : 1 = 1.\nProof. vm_compute. Zify.zify. reflexivity. Qed.\nLtac t := lia.",
                       "Definition d : nat := ltac:(vm_compute; exact 0).",
                       "(* Ltac t := xlia. *) Ltac t := idtac \"xlia\"."]:
            with self.subTest(source=source):
                self.assertEqual(solver_engine_failures(CORE, source, {}), [])

    def test_a_proof_does_not_hide_the_next_tactic(self):
        source = "Lemma l : True.\nProof. exact I. Qed.\nLtac t := xlia Lia.zchecker."
        self.assertEqual(len(solver_engine_failures(CORE, source, {})), 1)
        source = "Definition d := 1.\nLtac t := vm_compute."
        self.assertEqual(len(solver_engine_failures(CORE, source, {})), 1)

    def test_scope_allowlist_and_own_recursion(self):
        source = "Ltac t := Zify.zify; xlia Lia.zchecker."
        self.assertEqual(solver_engine_failures("ZesuSsz/Automation2/BoundedSolve.v", source, {}), [])
        self.assertEqual(solver_engine_failures("ZesuSsz/Automation/A.v", source, {}), [])
        self.assertEqual(solver_engine_failures("ZesuSsz/Proofs/Tests/A.v", source, {}), [])
        self.assertEqual(solver_engine_failures(CORE, source, {(CORE, "t"): "reason"}), [])
        self.assertEqual(solver_engine_failures(
            CORE, "Ltac2 rec zesu_saturate_seminaive () := zesu_saturate_seminaive ().", {}), [])

    def test_every_allowlist_entry_names_a_definition_with_a_reason(self):
        for (name, defined), reason in allowlist().items():
            with self.subTest(name=name, defined=defined):
                self.assertTrue(reason.strip())
                self.assertRegex((ROOT / name).read_text(), rf"Ltac2?\s+(?:rec\s+)?{defined}\b")


if __name__ == "__main__":
    unittest.main()
