Require Import isla.riscv64.riscv64.
Lemma array_counter_next_le (i limit : bv 64) :
  i <> limit -> (bv_unsigned i <= bv_unsigned limit)%Z ->
  (bv_unsigned (i + BV 64 1)%bv <= bv_unsigned limit)%Z.
Proof.
  intros Hne Hle. have HneZ : bv_unsigned i <> bv_unsigned limit.
  { intros Heq. apply Hne. apply bv_eq. exact Heq. }
  bv_solve.
Qed.
Print Assumptions array_counter_next_le.
Lemma array_counter_next_nat (i limit : bv 64) :
  i <> limit -> (bv_unsigned i <= bv_unsigned limit)%Z ->
  Z.to_nat (bv_unsigned (i + BV 64 1)%bv) = S (Z.to_nat (bv_unsigned i)).
Proof.
  intros Hne Hle. have HneZ : bv_unsigned i <> bv_unsigned limit.
  { intros Heq. apply Hne. apply bv_eq. exact Heq. }
  apply Nat2Z.inj. rewrite Nat2Z.inj_succ !Z2Nat.id; bv_solve.
Qed.
Print Assumptions array_counter_next_nat.
