Require Import ZesuSsz.Automation.AllLegacy.
Require Import ZesuSsz.Automation.ArrayCounterBounds.
Require Import isla.riscv64.riscv64.
Lemma test_array_counter_index (offset limit : bv 64) (bytes : list (bv 8)) :
  bv_unsigned limit = Z.of_nat (length bytes) ->
  offset <> limit -> (bv_unsigned offset <= bv_unsigned limit)%Z ->
  (Z.to_nat (bv_unsigned offset `div` 1) < length bytes)%nat.
Proof. apply array_counter_index_lt. Qed.
Print Assumptions test_array_counter_index.
