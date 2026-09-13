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

(* A binary Z bound also covers zero without expanding the Nat modulus. *)
Lemma zesu_counter_bound_z_iff count :
  (count < 2 ^ 64)%nat <-> (Z.of_nat count < 18446744073709551616)%Z.
Proof.
  rewrite Nat2Z.inj_lt Nat2Z.inj_pow.
  change (Z.of_nat count < 18446744073709551616 <->
    Z.of_nat count < 18446744073709551616). tauto.
Qed.
Print Assumptions zesu_counter_bound_z_iff.

Lemma zesu_counter_zero_z_bound count :
  (Z.of_nat count < 18446744073709551616)%Z ->
  Z_to_bv 64 (Z.of_nat count) = BV 64 0 -> count = 0%nat.
Proof.
  intros Hbound Hzero. apply (f_equal bv_unsigned) in Hzero.
  rewrite Z_to_bv_small in Hzero.
  - change (Z.of_nat count = 0) in Hzero. lia.
  - unfold bv_modulus. cbn. split; [apply Nat2Z.is_nonneg | exact Hbound].
Qed.
Global Instance zesu_counter_zero_z_shape count
    `{!TCFastDone ((Z.of_nat count < 18446744073709551616)%Z)} :
  SimplImplUnsafe true (Z_to_bv 64 (Z.of_nat count) = BV 64 0)
    (count = 0%nat).
Proof.
  intros Hzero. apply zesu_counter_zero_z_bound; [exact tc_fast_done | exact Hzero].
Qed.
Print Assumptions zesu_counter_zero_z_bound.
Print Assumptions zesu_counter_zero_z_shape.
