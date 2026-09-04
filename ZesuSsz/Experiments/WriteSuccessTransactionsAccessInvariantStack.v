From Coq Require Import ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Experiments.WriteSuccessAccessListsSpec.

Lemma write_success_transactions_access_invariant_stack
    `{!islaG Sigma} (sp : bv 64) (R : iProp Sigma)
    (Halign : bv_unsigned sp `mod` 16 = 0)
    (Hlow : 0x20000000 <= bv_unsigned sp - 48)
    (Hhigh : bv_unsigned sp + 1896 < 0x40000000) :
  R -∗
  ⌜bv_unsigned sp `mod` 16 = 0⌝ ∗
  ⌜0x20000000 <= bv_unsigned sp - 16⌝ ∗
  ⌜bv_unsigned sp + 1896 < 0x40000000⌝ ∗ R.
Proof.
  iIntros "HR".
  iSplit; [iPureIntro; exact Halign|].
  iSplit; [iPureIntro; lia|].
  iSplit; [iPureIntro; exact Hhigh|].
  iExact "HR".
Qed.
