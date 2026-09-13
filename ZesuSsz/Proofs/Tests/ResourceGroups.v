Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Automation.Resources.

Lemma resource_groups_array_frame `{!islaG Sigma}
    (address : Z) (bytes : list (bv 8)) (word : bv 64) (P : iProp Sigma) :
  (address ↦ₘ word ∗ (address + 8)%Z ↦ₘ∗ bytes ∗ P) -∗
  address ↦ₘ word ∗ (address + 8)%Z ↦ₘ∗ bytes ∗ P ∗ True.
Proof.
  iStartProof. iIntros "Hgroup". zesu_open_resource_groups. zesu_run.
Qed.
Print Assumptions resource_groups_array_frame.

Lemma resource_groups_nested `{!islaG Sigma}
    (address : Z) (word : bv 64) (P Q : iProp Sigma) :
  ((address ↦ₘ word ∗ P) ∗ Q) -∗ address ↦ₘ word ∗ P ∗ Q ∗ True.
Proof.
  iStartProof. iIntros "Hgroup". zesu_open_resource_groups. zesu_run.
Qed.
Print Assumptions resource_groups_nested.
