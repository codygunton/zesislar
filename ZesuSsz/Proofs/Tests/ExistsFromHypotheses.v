From Coq Require Import ZArith.ZArith Lists.List.
From stdpp.bitvector Require Import definitions.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Automation2.All.

Definition call_domain (arguments : list (bv 64)) (before : list (bv 8)) : Prop :=
  length before = length arguments.
Definition call_meaning (arguments : list (bv 64)) (before after : list (bv 8)) : Prop :=
  before = after.

(* A successor restates a call's facts over fresh names; the hypotheses set
   the witnesses. *)
Goal forall (first second : bv 64) (before after : list (bv 8)),
  call_domain [first; second] before -> call_meaning [first; second] before after ->
  exists (x y : bv 64) (before0 : list (bv 8)),
    call_domain [x; y] before0 /\ call_meaning [x; y] before0 after.
Proof. intros first second before after Hdomain Hmeaning. zesu_finish_exists_from_hypotheses. Qed.

(* A conjunct that no hypothesis states: the step does not close the goal. *)
Goal forall (first second : bv 64) (before : list (bv 8)),
  call_domain [first; second] before ->
  exists (x y : bv 64) (before0 : list (bv 8)),
    call_domain [x; y] before0 /\ call_meaning [x; y] before0 before0.
Proof.
  intros first second before Hdomain.
  Fail zesu_finish_exists_from_hypotheses.
  exists first, second, before. split; [exact Hdomain | reflexivity].
Qed.
