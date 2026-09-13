Require Import isla.riscv64.riscv64.

Lemma stack_align8_from16 (sp : bv 64) :
  bv_unsigned sp `mod` 16 = 0 -> bv_unsigned sp `mod` 8 = 0.
Proof. intros H. bv_solve. Qed.
Print Assumptions stack_align8_from16.
