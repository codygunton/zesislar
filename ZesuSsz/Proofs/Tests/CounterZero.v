Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.CounterZero.
Require Import isla.riscv64.riscv64.
Lemma test_counter_zero remaining :
  (S remaining < 2 ^ 64)%nat ->
  Z_to_bv 64 (Z.of_nat remaining) = BV 64 0 -> remaining = 0%nat.
Proof. apply zesu_counter_zero_bound. Qed.
Print Assumptions test_counter_zero.
