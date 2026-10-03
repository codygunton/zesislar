Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.Sets.call.
Import isla.riscv64.riscv64.
Open Scope Z_scope.

Lemma production_empty_word_array `{!islaG Sigma} `{!threadG}
    (base address : Z) (word : bv 64) (Hrange : 0 <= address <= 2 ^ 64) :
  base ↦ₘ∗ [word] -∗ address ↦ₘ∗ ([] : list (bv 64)) ∗ base ↦ₘ∗ [word].
Proof. zesu_block. Qed.
Print Assumptions production_empty_word_array.
