Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.

Lemma storage_keys_counter_decrement remaining :
  (Z_to_bv 64 (Z.of_nat (S remaining)) - BV 64 1)%bv =
  Z_to_bv 64 (Z.of_nat remaining).
Proof. rewrite Nat2Z.inj_succ. bv_solve. Qed.
Print Assumptions storage_keys_counter_decrement.

Lemma storage_keys_counter_zero remaining :
  Z.of_nat remaining < 18446744073709551616 ->
  Z_to_bv 64 (Z.of_nat remaining) = BV 64 0 -> remaining = 0%nat.
Proof.
  intros Hbound Hzero. apply (f_equal bv_unsigned) in Hzero.
  rewrite Z_to_bv_small in Hzero; [change (Z.of_nat remaining = 0) in Hzero; lia|].
  unfold bv_modulus. cbn. lia.
Qed.
Print Assumptions storage_keys_counter_zero.

Lemma storage_keys_pointer_advance (pointer : bv 64) base processed :
  0 <= base -> base + 32 * Z.of_nat processed + 32 < 1073741824 ->
  bv_unsigned pointer = base + 32 * Z.of_nat processed ->
  bv_unsigned (pointer + BV 64 32)%bv = base + 32 * Z.of_nat (S processed).
Proof. intros Hlow Hhigh Hposition. rewrite Nat2Z.inj_succ. bv_solve. Qed.
Print Assumptions storage_keys_pointer_advance.
