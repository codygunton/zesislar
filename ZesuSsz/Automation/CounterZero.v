Require Import isla.riscv64.riscv64.
Lemma zesu_counter_zero_bound remaining :
  (S remaining < 2 ^ 64)%nat ->
  Z_to_bv 64 (Z.of_nat remaining) = BV 64 0 -> remaining = 0%nat.
Proof.
  intros Hcount Hzero. apply Nat2Z.inj_lt in Hcount.
  rewrite Nat2Z.inj_pow Nat2Z.inj_succ in Hcount.
  change (Z.succ (Z.of_nat remaining) < 18446744073709551616) in Hcount.
  apply (f_equal bv_unsigned) in Hzero.
  rewrite Z_to_bv_small in Hzero; [change (Z.of_nat remaining = 0) in Hzero; lia|].
  unfold bv_modulus. cbn. lia.
Qed.
Global Instance zesu_counter_zero_shape remaining
    `{!TCFastDone ((S remaining < 2 ^ 64)%nat)} :
  SimplImplUnsafe true (Z_to_bv 64 (Z.of_nat remaining) = BV 64 0)
    (remaining = 0%nat).
Proof. intros Hzero. apply zesu_counter_zero_bound; [exact tc_fast_done|exact Hzero]. Qed.
Print Assumptions zesu_counter_zero_bound.
Print Assumptions zesu_counter_zero_shape.
