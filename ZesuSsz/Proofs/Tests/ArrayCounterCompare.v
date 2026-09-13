Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.ArrayCounterCompare.
Require Import isla.riscv64.riscv64.
Lemma test_array_counter_compare (i limit : bv 64) :
  i <> limit -> (bv_unsigned i <= bv_unsigned limit)%Z ->
  Z.compare (bv_unsigned (i + BV 64 1)%bv) (bv_unsigned limit) = Gt -> False.
Proof. apply array_counter_next_not_gt. Qed.
Print Assumptions test_array_counter_compare.
