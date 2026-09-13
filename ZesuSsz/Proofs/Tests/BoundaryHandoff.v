Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
From iris.proofmode Require Import environments.

Lemma test_boundary_handoff `{!islaG Sigma} `{!threadG}
    (value : bv 64) (P : iProp Sigma) :
  "x10" ↦ᵣ RVal_Bits value ∗ P ∗ True -∗
  ∃ x : bv 64 *ₗ (), "x10" ↦ᵣ RVal_Bits x.1ₗ ∗ P ∗ True.
Proof.
  iStartProof.
  zesu_run_until ltac:(fun _ => lazymatch goal with
    |- envs_entails _ (∃ x : bv 64 *ₗ (), _) => idtac
  end).
  iExists (value, tt)ₗ. zesu_run.
Qed.

Print Assumptions test_boundary_handoff.
