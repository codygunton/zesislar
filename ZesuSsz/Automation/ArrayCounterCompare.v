Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Automation.ArrayCounterStep.
Lemma array_counter_next_not_gt (i limit : bv 64) :
  i <> limit -> (bv_unsigned i <= bv_unsigned limit)%Z ->
  Z.compare (bv_unsigned (i + BV 64 1)%bv) (bv_unsigned limit) = Gt -> False.
Proof.
  intros Hne Hle Hgt. apply Z.compare_gt_iff in Hgt.
  have Hnext := array_counter_next_le i limit Hne Hle. lia.
Qed.
Print Assumptions array_counter_next_not_gt.
