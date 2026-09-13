Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.StackAlignment.
Require Import isla.riscv64.riscv64.

Lemma test_stack_alignment_with_counter (sp : bv 64) (remaining : nat) :
  (S remaining < 2 ^ 64)%nat ->
  bv_unsigned sp `mod` 16 = 0 -> bv_unsigned sp `mod` 8 = 0.
Proof. intros Hcount Halign. apply stack_align8_from16. exact Halign. Qed.
Print Assumptions test_stack_alignment_with_counter.
