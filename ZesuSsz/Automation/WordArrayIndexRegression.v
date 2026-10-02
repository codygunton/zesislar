Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.WordArrayIndex.
Require Import ZesuSsz.Contracts.IslarisMemory.
Require Import ZesuSsz.Automation.Sets.call.
Require Import isla.riscv64.riscv64.
Open Scope Z_scope.

Lemma constant_word_index_regression (base : Z) :
  array_region_start 64 (base + 936) (base + 984) = 6%nat.
Proof. zesu_constant_word_array_index. reflexivity. Qed.

Lemma empty_word_array_preserves_owner `{!islaG Sigma} `{!threadG}
    (base address : Z) (word : bv 64)
    (Hrange : 0 <= address <= 2 ^ 64) :
  base ↦ₘ∗ [word] -∗
  address ↦ₘ∗ ([] : list (bv 64)) ∗ base ↦ₘ∗ [word].
Proof. iIntros "Hword". zesu_run. Qed.

Print Assumptions constant_word_index_regression.
Print Assumptions empty_word_array_preserves_owner.
