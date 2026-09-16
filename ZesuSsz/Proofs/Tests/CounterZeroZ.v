Require Import ZesuSsz.Automation.AllLegacy.
Require Import ZesuSsz.Automation.CounterZero.
Require Import isla.riscv64.riscv64.

Lemma test_counter_bound_z_iff count :
  (count < 2 ^ 64)%nat <-> (Z.of_nat count < 18446744073709551616)%Z.
Proof. apply zesu_counter_bound_z_iff. Qed.
Print Assumptions test_counter_bound_z_iff.

Lemma test_counter_zero_z count :
  (Z.of_nat count < 18446744073709551616)%Z ->
  Z_to_bv 64 (Z.of_nat count) = BV 64 0 -> count = 0%nat.
Proof. apply zesu_counter_zero_z_bound. Qed.
Print Assumptions test_counter_zero_z.

Lemma test_counter_succ_nonzero_z count :
  (Z.of_nat (S count) < 18446744073709551616)%Z ->
  Z_to_bv 64 (Z.of_nat (S count)) <> BV 64 0.
Proof.
  intros Hbound Hzero.
  have Hcount := zesu_counter_zero_z_bound (S count) Hbound Hzero.
  discriminate.
Qed.
Print Assumptions test_counter_succ_nonzero_z.
