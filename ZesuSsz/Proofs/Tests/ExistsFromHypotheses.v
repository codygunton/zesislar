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

(* The final finisher reaches the step on a context with no implication pair. *)
Goal forall (first second : bv 64) (before after : list (bv 8)),
  call_domain [first; second] before -> call_meaning [first; second] before after ->
  exists (x y : bv 64) (before0 : list (bv 8)),
    call_domain [x; y] before0 /\ call_meaning [x; y] before0 after.
Proof. intros first second before after Hdomain Hmeaning. zesu_finish_final_pure. Qed.

(* A binder no conjunct mentions stays a goal of its type after `eexists`:
   it takes `inhabitant`, so no hypothesis of that type is needed (before,
   the step searched one and failed here: the context holds no word). *)
Goal forall (before after : list (bv 8)),
  call_meaning [] before after ->
  exists (_ : bv 64) (before0 : list (bv 8)), call_meaning [] before0 after.
Proof. intros before after Hmeaning. zesu_finish_exists_from_hypotheses. Qed.

(* A type without an `Inhabited` instance: the first hypothesis of the type. *)
Inductive exists_token := ExistsToken.
Goal forall (token : exists_token) (before after : list (bv 8)),
  call_meaning [] before after ->
  exists (_ : exists_token) (before0 : list (bv 8)), call_meaning [] before0 after.
Proof. intros token before after Hmeaning. zesu_finish_exists_from_hypotheses. Qed.

(* Unused binders over a context of words and a conjunct no hypothesis states:
   each witness is chosen once, so the step fails after one pass over the
   conjuncts (before, it tried 8^5 witness combinations first). *)
Goal forall (w0 w1 w2 w3 w4 w5 w6 w7 : bv 64) (before : list (bv 8)),
  call_domain [w0; w1; w2; w3; w4; w5; w6; w7] before ->
  exists (_ _ _ _ _ : bv 64) (before0 : list (bv 8)),
    call_domain [w0; w1; w2; w3; w4; w5; w6; w7] before0 /\
    call_meaning [w0] before0 before0.
Proof.
  intros w0 w1 w2 w3 w4 w5 w6 w7 before Hdomain.
  Fail zesu_finish_exists_from_hypotheses.
  exists w0, w0, w0, w0, w0, before. split; [exact Hdomain | reflexivity].
Qed.

(* An equation whose two sides are the same term once the witnesses are set
   (a call record restating a returned word) closes by `reflexivity`; before,
   the step looked for a hypothesis stating it and failed here. *)
Goal forall (first : bv 64) (before : list (bv 8)),
  call_domain [first] before ->
  exists (x : bv 64) (before0 : list (bv 8)),
    call_domain [x] before0 /\ Z_to_bv 64 (bv_unsigned x) = Z_to_bv 64 (bv_unsigned first).
Proof. intros first before Hdomain. zesu_finish_exists_from_hypotheses. Qed.

(* Only a syntactic match: an equation that holds by computation is left. *)
Goal forall (first : bv 64) (before : list (bv 8)),
  call_domain [first] before ->
  exists (x : bv 64) (before0 : list (bv 8)), call_domain [x] before0 /\ (1 + 1 = 2)%Z.
Proof.
  intros first before Hdomain.
  Fail zesu_finish_exists_from_hypotheses.
  exists first, before. split; [exact Hdomain | reflexivity].
Qed.
