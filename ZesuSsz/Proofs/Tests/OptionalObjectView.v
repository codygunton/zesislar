Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMemory.

Lemma optional_object_view `{!islaG Sigma} `{!threadG}
    (pointer : Z) (value : bv 64) (tag : bv 8) (P : iProp Sigma) :
  pointer ↦ₘ value ∗ (pointer + 8) ↦ₘ tag ∗ P ∗ True -∗
  pointer ↦ₘ∗ (bytes_of_u64s [value] ++ [tag]) ∗ P ∗ True.
Proof. iStartProof. zesu_run. Qed.

Print Assumptions optional_object_view.

Lemma optional_object_view_return `{!islaG Sigma} `{!threadG}
    (pointer : Z) (value : bv 64) (tag : bv 8) (P : iProp Sigma) :
  pointer ↦ₘ∗ (bytes_of_u64s [value] ++ [tag]) ∗ P ∗ True -∗
  pointer ↦ₘ value ∗ (pointer + 8) ↦ₘ tag ∗ P ∗ True.
Proof. iStartProof. zesu_run. Qed.

Print Assumptions optional_object_view_return.
