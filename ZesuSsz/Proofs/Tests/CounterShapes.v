Require Import ZesuSsz.Automation.AllLegacy.
Require Import ZesuSsz.Automation.CounterShapes.
Require Import isla.riscv64.riscv64.

Lemma test_counter_shape remaining :
  (Z_to_bv 64 (Z.of_nat (S remaining)) + BV 64 18446744073709551615)%bv <> BV 64 0 ->
  exists n, remaining = S n.
Proof. apply zesu_counter_succ_nonzero. Qed.
Print Assumptions test_counter_shape.

Lemma test_counter_decrement remaining :
  (Z_to_bv 64 (Z.of_nat (S remaining)) + BV 64 18446744073709551615)%bv =
  Z_to_bv 64 (Z.of_nat remaining).
Proof. apply zesu_counter_succ_decrement. Qed.
Print Assumptions test_counter_decrement.
