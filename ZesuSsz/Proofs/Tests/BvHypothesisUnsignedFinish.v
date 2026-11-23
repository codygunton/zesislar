From Coq Require Import ZArith.ZArith.
From stdpp Require Import bitvector.definitions.
Require Import ZesuSsz.Automation2.All.
Require Import ZesuSsz.Automation2.BitvectorHypothesisUnsigned.
Local Open Scope Z_scope.

(* A branch condition can exist only as a bit-vector (dis)equality while the
   goal states it over `bv_unsigned`. The final finisher restates the
   hypothesis over `bv_unsigned`; lia and bv_solve do not read it. *)
Record unsigned_args := {
  unsigned_head : bv 64; unsigned_low : bv 64; unsigned_high : bv 64 }.

Lemma final_pure_reads_bv_equality (args : unsigned_args) :
  unsigned_head args = 0%bv -> bv_unsigned (unsigned_head args) = 0.
Proof. intros Hzero. zesu_finish_final_pure. Qed.

Lemma final_pure_reads_bv_disequality (args : unsigned_args) :
  bv_or (unsigned_low args) (unsigned_high args) <> 0%bv ->
  bv_unsigned (bv_or (unsigned_low args) (unsigned_high args)) <> 0.
Proof. intros Hnonzero. zesu_finish_final_pure. Qed.

Lemma final_pure_reads_reversed_equality (args : unsigned_args) :
  1%bv = unsigned_head args -> 1 = bv_unsigned (unsigned_head args).
Proof. intros Hone. zesu_finish_final_pure. Qed.

(* The restated fact must decide the goal: a different constant stays open,
   and the finisher still succeeds on it, as before. *)
Lemma final_pure_keeps_unrelated_constant (args : unsigned_args) :
  unsigned_head args = 0%bv -> True.
Proof.
  intros Hzero.
  assert_fails (assert (bv_unsigned (unsigned_head args) = 1)
    by zesu_bv_hypothesis_unsigned).
  assert_succeeds (assert (bv_unsigned (unsigned_head args) = 1);
    [zesu_finish_final_pure |]).
  exact I.
Qed.
