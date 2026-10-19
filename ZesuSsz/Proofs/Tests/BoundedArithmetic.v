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

Print Assumptions test_byte_index_fact_selection.

Lemma test_constant_solver_rejects_open_terms (value : bv 64) :
  value = value.
Proof. Fail zesu_finish_constant. reflexivity. Qed.

Lemma test_constant_solver_closed_terms :
  (BV 64 1 + BV 64 2)%bv = BV 64 3.
Proof. zesu_finish_constant. Qed.

Print Assumptions test_constant_solver_rejects_open_terms.
Print Assumptions test_constant_solver_closed_terms.
