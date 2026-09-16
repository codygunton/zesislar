Require Import ZesuSsz.Automation.AllLegacy.
Require Import ZesuSsz.Automation.ArrayCounterStep.
Require Import isla.riscv64.riscv64.
Lemma test_array_counter_next (i limit : bv 64) :
  i <> limit -> (bv_unsigned i <= bv_unsigned limit)%Z ->
  Z.to_nat (bv_unsigned (i + BV 64 1)%bv) = S (Z.to_nat (bv_unsigned i)).
Proof. apply array_counter_next_nat. Qed.
Print Assumptions test_array_counter_next.
