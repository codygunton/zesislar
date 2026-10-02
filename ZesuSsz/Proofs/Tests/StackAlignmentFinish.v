Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.

Lemma stack_alignment_default_guard (sp : bv 64) :
  bv_extract 0 4 sp = BV 4 0 ->
  bv_unsigned (sp + BV 64 18446744073709549616)%bv `mod` 8 = 0.
Proof.
  intros Halign. Fail zesu_finish_pointer_alignment.
  bv_simplify_arith Halign. bv_solve.
Qed.

Require Import ZesuSsz.Automation.Sets.call.

Lemma stack_alignment_prologue (sp : bv 64) :
  bv_extract 0 4 sp = BV 4 0 ->
  bv_unsigned (sp + BV 64 18446744073709549616)%bv `mod` 8 = 0.
Proof. intros Halign. zesu_finish_pointer_alignment. Qed.

Lemma stack_alignment_positive_offset (sp : bv 64) :
  bv_extract 0 4 sp = BV 4 0 ->
  bv_unsigned (sp + BV 64 16)%bv `mod` 16 = 0.
Proof. intros Halign. zesu_finish_pointer_alignment. Qed.

Lemma stack_alignment_finisher (sp : bv 64) (remaining : nat) :
  (S remaining < 2 ^ 64)%nat ->
  bv_extract 0 4 sp = BV 4 0 ->
  bv_unsigned (sp + BV 64 18446744073709549616)%bv `mod` 8 = 0.
Proof. intros Hcount Halign. zesu_finish_pure_goal. Qed.

Print Assumptions stack_alignment_default_guard.
Print Assumptions stack_alignment_prologue.
Print Assumptions stack_alignment_positive_offset.
Print Assumptions stack_alignment_finisher.
