Require Import ZesuSsz.Automation.All.
From stdpp.bitvector Require Import tactics.

(* Symbolic candidates must leave the context intact. *)
Lemma zesu_stack_closed_term_regression (x : Z) : x = x.
Proof.
  zesu_stack_closed_term (3 + 4)%Z.
  Fail zesu_stack_closed_term x.
  Fail zesu_stack_closed_term (x + 4)%Z.
  Fail zesu_stack_closed_term (fun n : Z => n).
  Fail zesu_stack_closed_term (forall n : Z, n = n).
  zesu_stack_closed_term (let n := 3%Z in n + 4)%Z.
  zesu_stack_closed_term ((fun n : Z => n + 4) 3)%Z.
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

Lemma zesu_stack_closed_nested_aliases : True.
Proof.
  pose (firstConstant := (3 + 4)%Z).
  pose (secondConstant := (firstConstant + 5)%Z).
  zesu_stack_closed_term secondConstant.
  exact I.
Qed.

Lemma zesu_stack_closed_alias_evar : True.
Proof.
  evar (unknown : Z).
  pose (hiddenAlias := (unknown + 1)%Z).
  Fail zesu_stack_closed_term hiddenAlias.
  Fail let body := eval unfold unknown in unknown in
    zesu_stack_closed_term body.
  let body := eval unfold unknown in unknown in is_evar body.
  instantiate (unknown := 0%Z).
  exact I.
Qed.

Lemma zesu_stack_reduce_closed_regression (x : Z) : (x + (3 + 4) = x + 7)%Z.
Proof.
  zesu_stack_reduce_closed (3 + 4)%Z.
  reflexivity.
Qed.
