Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.ArrayCopyFinish.
Require Import isla.riscv64.riscv64.

Lemma test_array_copy_counter (i limit : bv 64) :
  i <> limit -> (bv_unsigned i <= bv_unsigned limit)%Z ->
  (bv_unsigned (i + BV 64 1)%bv <= bv_unsigned limit)%Z.
Proof. intros Hne Hle. zesu_copy_finish. Qed.
Print Assumptions test_array_copy_counter.
