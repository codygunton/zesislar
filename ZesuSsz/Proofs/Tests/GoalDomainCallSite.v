From Coq Require Import ZArith.ZArith Lists.List.
From stdpp.bitvector Require Import definitions.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Interfaces.DecodeItem.
Require Import ZesuSsz.Contracts.ParentHeaderContract.
Import ListNotations.
Require Import ZesuSsz.Automation2.All.
Local Open Scope Z_scope.

(* A caller's first decodeItem call: the result buffer sits in the caller's
   frame, the input is the caller's input, and the callee's sealed domain
   follows from the caller's domain by frame arithmetic, through the
   interface's introduction lemma and the stated precondition. *)
Lemma goal_domain_first_call (args : ParentHeaderArgs) (x13 x14 x15 x16 x17 : bv 64)
    (values : list (bv 8)) :
  parentHeaderArgsWellFormed args ->
  length values = 40%nat ->
  decodeItemCallDomain
    (decodeItemCallDataArgs
       [(parentHeaderStackPointer args + 18446744073709551216 + 400 +
         18446744073709551224)%bv; parentHeaderInputPointer args;
        parentHeaderInputLength args; x13; x14; x15; x16; x17]
       (parentHeaderStackPointer args + 18446744073709551216)
       (bv_unsigned (parentHeaderInputEnd args))
       (parentHeaderInputBytes args) values).
Proof. intros. zesu_finish_goal_domain. Qed.

(* The search's finisher reaches the step on the same goal. *)
Lemma goal_domain_first_call_finish (args : ParentHeaderArgs) (x13 x14 x15 x16 x17 : bv 64)
    (values : list (bv 8)) :
  parentHeaderArgsWellFormed args ->
  length values = 40%nat ->
  decodeItemCallDomain
    (decodeItemCallDataArgs
       [(parentHeaderStackPointer args + 18446744073709551216 + 400 +
         18446744073709551224)%bv; parentHeaderInputPointer args;
        parentHeaderInputLength args; x13; x14; x15; x16; x17]
       (parentHeaderStackPointer args + 18446744073709551216)
       (bv_unsigned (parentHeaderInputEnd args))
       (parentHeaderInputBytes args) values).
Proof. intros. zesu_finish. Qed.

(* Without the buffer's length the domain does not follow, and the step
   leaves the goal unchanged. *)
Lemma goal_domain_needs_length (args : ParentHeaderArgs) (x13 x14 x15 x16 x17 : bv 64)
    (values : list (bv 8)) :
  parentHeaderArgsWellFormed args ->
  decodeItemCallDomain
    (decodeItemCallDataArgs
       [(parentHeaderStackPointer args + 18446744073709551216 + 400 +
         18446744073709551224)%bv; parentHeaderInputPointer args;
        parentHeaderInputLength args; x13; x14; x15; x16; x17]
       (parentHeaderStackPointer args + 18446744073709551216)
       (bv_unsigned (parentHeaderInputEnd args))
       (parentHeaderInputBytes args) values) ->
  decodeItemCallDomain
    (decodeItemCallDataArgs
       [(parentHeaderStackPointer args + 18446744073709551216 + 400 +
         18446744073709551224)%bv; parentHeaderInputPointer args;
        parentHeaderInputLength args; x13; x14; x15; x16; x17]
       (parentHeaderStackPointer args + 18446744073709551216)
       (bv_unsigned (parentHeaderInputEnd args))
       (parentHeaderInputBytes args) values).
Proof.
  intros Hwf Hdomain.
  Fail (clear Hdomain; zesu_finish_goal_domain).
  exact Hdomain.
Qed.

(* A goal with no registered head and no registered introduction: the step
   fails at once. *)
Goal forall n : Z, n = n + 0.
Proof.
  intros n. Fail zesu_finish_goal_domain. lia.
Qed.

(* A call's domain restated over a fresh name, as an existential (a shelved
   side condition). lia and bv_solve never choose a witness: `split` would
   leave it as a goal of type bv 64, which they close only by refuting the
   whole context. The step refuses the existential at once, even on a
   context that refutes; with the witness chosen it closes the domain. *)
Lemma goal_domain_existential (args : ParentHeaderArgs) (x13 x14 x15 x16 x17 : bv 64)
    (values : list (bv 8)) :
  parentHeaderArgsWellFormed args ->
  length values = 40%nat ->
  0 < 0 ->
  exists y : bv 64, decodeItemCallDomain
    (decodeItemCallDataArgs
       [(parentHeaderStackPointer args + 18446744073709551216 + 400 +
         18446744073709551224)%bv; parentHeaderInputPointer args;
        parentHeaderInputLength args; y; x14; x15; x16; x17]
       (parentHeaderStackPointer args + 18446744073709551216)
       (bv_unsigned (parentHeaderInputEnd args))
       (parentHeaderInputBytes args) values).
Proof.
  intros.
  Fail zesu_finish_goal_domain.
  exists x13. zesu_finish_goal_domain.
Qed.

(* The same existential as a conjunct: the step refuses that part. *)
Lemma goal_domain_existential_part (args : ParentHeaderArgs) (x13 x14 x15 x16 x17 : bv 64)
    (values : list (bv 8)) :
  parentHeaderArgsWellFormed args ->
  length values = 40%nat ->
  0 < 0 ->
  0 <= bv_unsigned x13 /\
  exists y : bv 64, decodeItemCallDomain
    (decodeItemCallDataArgs
       [(parentHeaderStackPointer args + 18446744073709551216 + 400 +
         18446744073709551224)%bv; parentHeaderInputPointer args;
        parentHeaderInputLength args; y; x14; x15; x16; x17]
       (parentHeaderStackPointer args + 18446744073709551216)
       (bv_unsigned (parentHeaderInputEnd args))
       (parentHeaderInputBytes args) values).
Proof.
  intros.
  Fail zesu_finish_goal_domain.
  split; [lia | exists x13; zesu_finish_goal_domain].
Qed.
