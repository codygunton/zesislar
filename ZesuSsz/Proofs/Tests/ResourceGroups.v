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

Lemma resource_array_ram_offset `{!islaG Sigma}
    (pointer : bv 64) (bytes : list (bv 8)) :
  0x20000000 <= bv_unsigned pointer ->
  bv_unsigned pointer + 32 < 0x40000000 ->
  (bv_unsigned pointer + 16)%Z ↦ₘ∗ bytes -∗
  bv_unsigned (pointer + BV 64 16)%bv ↦ₘ∗ bytes ∗ True.
Proof.
  intros Hlower Hupper. iStartProof. iIntros "Hbytes".
  zesu_normalize_resource_addresses. zesu_run.
Qed.
Print Assumptions resource_array_ram_offset.

Lemma resource_groups_pure `{!islaG Sigma}
    (address : Z) (word : bv 64) (n : nat) :
  (address ↦ₘ word ∗ ⌜n = 0%nat⌝) -∗
  address ↦ₘ word ∗ ⌜n <= 1⌝ ∗ True.
Proof.
  iStartProof. iIntros "Hgroup". zesu_open_resource_groups. zesu_run.
Qed.
Print Assumptions resource_groups_pure.
