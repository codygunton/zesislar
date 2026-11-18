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

(* The words at bytes 0..7, 8..15 and 24..31 of a decodeItem output, in the
   load form the block generator renders. *)
Notation outWordAt k bytes :=
  (bv_concat 64%N (bv_concat 56%N (bv_concat 48%N (bv_concat 40%N (bv_concat 32%N (bv_concat 24%N
    (bv_concat 16%N (List.nth (k + 7)%nat bytes (BV 8%N 0%Z)) (List.nth (k + 6)%nat bytes (BV 8%N 0%Z)))
    (List.nth (k + 5)%nat bytes (BV 8%N 0%Z))) (List.nth (k + 4)%nat bytes (BV 8%N 0%Z)))
    (List.nth (k + 3)%nat bytes (BV 8%N 0%Z))) (List.nth (k + 2)%nat bytes (BV 8%N 0%Z)))
    (List.nth (k + 1)%nat bytes (BV 8%N 0%Z))) (List.nth k bytes (BV 8%N 0%Z))) (only parsing).

(* A third call over the rest of a payload: the first call's payload pointer
   and length are kept under names, the second call decodes the payload's
   slice, and the third gets the cursor advanced by the second call's
   consumed count. Its domain reads the kept names' values, the second
   call's window over the input, the consumed bound that decodeItem's
   interface derives from the sealed second call, and the input's range in
   the caller's folded precondition; plain lia and bv_solve see none of
   them. *)
Lemma goal_domain_kept_cursor (args : ParentHeaderArgs)
    (kept_ptr kept_len a13 a14 a15 a16 a17 b13 b14 b15 b16 b17 x13 x14 x15 x16 x17 : bv 64)
    (before before0 values first second : list (bv 8)) :
  parentHeaderArgsWellFormed args ->
  length before = 40%nat -> length before0 = 40%nat -> length values = 40%nat ->
  decodeItemCallDomain
    (decodeItemCallDataArgs
       [(parentHeaderStackPointer args + 18446744073709551216 + 400 +
         18446744073709551224)%bv; parentHeaderInputPointer args;
        parentHeaderInputLength args; a13; a14; a15; a16; a17]
       (parentHeaderStackPointer args + 18446744073709551216)
       (bv_unsigned (parentHeaderInputEnd args))
       (parentHeaderInputBytes args) before) ->
  decodeItemCallMeaning
    (decodeItemCallDataArgs
       [(parentHeaderStackPointer args + 18446744073709551216 + 400 +
         18446744073709551224)%bv; parentHeaderInputPointer args;
        parentHeaderInputLength args; a13; a14; a15; a16; a17]
       (parentHeaderStackPointer args + 18446744073709551216)
       (bv_unsigned (parentHeaderInputEnd args))
       (parentHeaderInputBytes args) before) first ->
  zesu_named_eq kept_ptr (outWordAt 0 first) ->
  zesu_named_eq kept_len (outWordAt 8 first) ->
  bv_unsigned (parentHeaderInputPointer args) <= bv_unsigned kept_ptr ->
  bv_unsigned kept_ptr + bv_unsigned kept_len <=
    bv_unsigned (parentHeaderInputPointer args) + bv_unsigned (parentHeaderInputLength args) ->
  decodeItemCallDomain
    (decodeItemCallDataArgs
       [(parentHeaderStackPointer args + 18446744073709551216 + 400 +
         18446744073709551280)%bv; kept_ptr; kept_len; b13; b14; b15; b16; b17]
       (parentHeaderStackPointer args + 18446744073709551216)
       (bv_unsigned (parentHeaderInputEnd args))
       (take (Z.to_nat (bv_unsigned kept_len))
          (drop (Z.to_nat (bv_unsigned kept_ptr - bv_unsigned (parentHeaderInputPointer args)))
             (parentHeaderInputBytes args))) before0) ->
  decodeItemCallMeaning
    (decodeItemCallDataArgs
       [(parentHeaderStackPointer args + 18446744073709551216 + 400 +
         18446744073709551280)%bv; kept_ptr; kept_len; b13; b14; b15; b16; b17]
       (parentHeaderStackPointer args + 18446744073709551216)
       (bv_unsigned (parentHeaderInputEnd args))
       (take (Z.to_nat (bv_unsigned kept_len))
          (drop (Z.to_nat (bv_unsigned kept_ptr - bv_unsigned (parentHeaderInputPointer args)))
             (parentHeaderInputBytes args))) before0) second ->
  decodeItemCallDomain
    (decodeItemCallDataArgs
       [(parentHeaderStackPointer args + 18446744073709551216 + 400 +
         18446744073709551280)%bv; (kept_ptr + outWordAt 24 second)%bv;
        (kept_len - outWordAt 24 second)%bv; x13; x14; x15; x16; x17]
       (parentHeaderStackPointer args + 18446744073709551216)
       (bv_unsigned (parentHeaderInputEnd args))
       (take (Z.to_nat (bv_unsigned (kept_len - outWordAt 24 second)))
          (drop (Z.to_nat (bv_unsigned (kept_ptr + outWordAt 24 second) -
                           bv_unsigned (parentHeaderInputPointer args)))
             (parentHeaderInputBytes args))) values).
Proof. intros. zesu_finish_goal_domain. Qed.
