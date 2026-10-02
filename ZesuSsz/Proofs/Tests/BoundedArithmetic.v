Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Automation.Sets.call.

Lemma test_byte_index_fact_selection (bytes : list (bv 8))
    (index : nat) (pointer other : bv 64) (base : Z) :
  bv_unsigned pointer = (base + Z.of_nat index)%Z ->
  (index + 31 < length bytes)%nat ->
  bv_unsigned other mod 17 = 0%Z ->
  (index + 20 < length bytes)%nat.
Proof.
  intros Hindex Hbound Hunrelated.
  zesu_select_index_facts bytes index pointer base.
  Fail pose proof Hunrelated.
  zesu_finish_lia.
Qed.

Lemma test_arithmetic_timeout_retains_goal : True.
Proof.
  zesu_bounded_arithmetic ltac:(idtac).
  Fail zesu_bounded_arithmetic_with 1
    ltac:(let rec spin dummy := spin dummy in spin tt).
  exact I.
Qed.

Print Assumptions test_byte_index_fact_selection.
Print Assumptions test_arithmetic_timeout_retains_goal.
