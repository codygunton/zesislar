Require Import ZesuSsz.Automation.All.
From stdpp.bitvector Require Import tactics.

(* Symbolic candidates must leave the context intact. *)
Lemma zesu_stack_closed_term_regression (x : Z) : x = x.
Proof.
  zesu_stack_closed_term (3 + 4)%Z.
  Fail zesu_stack_closed_term x.
  zesu_stack_closed_term (let n := 3%Z in n + 4)%Z.
  pose (localConstant := (3 + 4)%Z).
  zesu_stack_closed_term localConstant.
  pose (localSymbolic := (x + 4)%Z).
  Fail zesu_stack_closed_term localSymbolic.
  evar (unknown : Z).
  Fail zesu_stack_closed_term unknown.
  instantiate (unknown := 0%Z).
  clear unknown.
  reflexivity.
Qed.

Lemma zesu_stack_reduce_closed_regression (x : Z) : (x + (3 + 4) = x + 7)%Z.
Proof.
  zesu_stack_reduce_closed (3 + 4)%Z.
  reflexivity.
Qed.
