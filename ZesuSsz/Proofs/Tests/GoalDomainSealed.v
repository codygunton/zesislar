From Coq Require Import ZArith.ZArith Lists.List.
From stdpp.bitvector Require Import definitions.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Interfaces.DecodeItem.
Require Import ZesuSsz.Contracts.ParentHeaderContract.
Import ListNotations.
Require Import ZesuSsz.Automation2.All.
Local Open Scope Z_scope.

(* A sealed callee domain (a goal with a registered introduction) goes to
   its introduction in the finisher's solver stage, never to a bare lia or
   bv_solve: on an opaque goal those only search the context for a
   contradiction (Finish.v, GoalDomain.zesu_goal_domain_sealed). *)

(* The guard: a sealed domain has a registered introduction; an arithmetic
   goal has none. *)
Goal forall (args : ParentHeaderArgs) (x13 x14 x15 x16 x17 : bv 64) (values : list (bv 8)),
  decodeItemCallDomain
    (decodeItemCallDataArgs
       [(parentHeaderStackPointer args + 18446744073709551216 + 400 +
         18446744073709551224)%bv; parentHeaderInputPointer args;
        parentHeaderInputLength args; x13; x14; x15; x16; x17]
       (parentHeaderStackPointer args + 18446744073709551216)
       (bv_unsigned (parentHeaderInputEnd args))
       (parentHeaderInputBytes args) values) -> True.
Proof.
  intros args x13 x14 x15 x16 x17 values H.
  assert (decodeItemCallDomain
    (decodeItemCallDataArgs
       [(parentHeaderStackPointer args + 18446744073709551216 + 400 +
         18446744073709551224)%bv; parentHeaderInputPointer args;
        parentHeaderInputLength args; x13; x14; x15; x16; x17]
       (parentHeaderStackPointer args + 18446744073709551216)
       (bv_unsigned (parentHeaderInputEnd args))
       (parentHeaderInputBytes args) values)).
  { ZesuSsz.Automation2.GoalDomain.zesu_goal_domain_sealed. exact H. }
  exact I.
Qed.

Goal forall n : Z, n = n + 0.
Proof. intros n. Fail ZesuSsz.Automation2.GoalDomain.zesu_goal_domain_sealed. lia. Qed.

(* A large context of unrelated arithmetic facts: the finisher closes the
   sealed domain through its introduction. *)
Lemma goal_domain_sealed_large_context (args : ParentHeaderArgs) (x13 x14 x15 x16 x17 : bv 64)
    (values : list (bv 8)) (a b c d e f g h : Z) :
  parentHeaderArgsWellFormed args ->
  length values = 40%nat ->
  0 <= a * b <= c * d -> c * d <= e * f + g * h -> 0 <= e * f -> a * c <= b * d ->
  e * g <= f * h -> 0 <= g * h * a -> b * b <= c * c + d * d ->
  decodeItemCallDomain
    (decodeItemCallDataArgs
       [(parentHeaderStackPointer args + 18446744073709551216 + 400 +
         18446744073709551224)%bv; parentHeaderInputPointer args;
        parentHeaderInputLength args; x13; x14; x15; x16; x17]
       (parentHeaderStackPointer args + 18446744073709551216)
       (bv_unsigned (parentHeaderInputEnd args))
       (parentHeaderInputBytes args) values).
Proof. intros. zesu_finish. Qed.

(* A part over a frame slot: its address is a modular sum with closed words,
   its alignment a divisibility. Over the facts that share its atoms (the
   stack pointer's range and alignment) it closes; the unrelated facts of
   the context take no part. A part the selected facts do not give fails at
   once: no solver runs over the whole context. *)
Lemma goal_domain_part_frame_slot (sp : bv 64) (a b c d e f : Z) :
  2684355264 <= bv_unsigned sp <= 3221225472 ->
  bv_unsigned sp mod 16 = 0 ->
  0 <= a * b <= c * d -> c * d <= e * f -> a * c <= b * d ->
  (8 | (bv_unsigned sp + bv_unsigned (BV 64 18446744073709551040)) mod 2 ^ 64).
Proof. intros. ZesuSsz.Automation2.GoalDomain.zesu_goal_domain_part. Qed.

Goal forall (sp : bv 64) (a b c d e f : Z),
  0 <= a * b <= c * d -> c * d <= e * f -> a * c <= b * d ->
  (8 | (bv_unsigned sp + 8) mod 2 ^ 64) \/ True.
Proof.
  intros. Fail (left; ZesuSsz.Automation2.GoalDomain.zesu_goal_domain_part).
  right. exact I.
Qed.
