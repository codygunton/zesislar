Require Import isla.riscv64.riscv64.
From Coq Require Import ZArith.
Require Import ZesuSsz.Automation2.All.
Open Scope Z_scope.

#[local] Instance integer_return_enabled : ZesuStepIntegerReturn := I.

(* The return-fault arm of a `ret` whose target is a saved return-address
   word (a record field of type `bv 64`, no `Z_to_bv` image) is refuted from
   the word's alignment. *)

Record SavedFrame := { savedReturnAddress : bv 64 }.

Definition savedReturnFaultBit (ret : bv 64) : bv 1 :=
  bv_extract 0 1 (bv_shiftr
    (bv_or (bv_and (bv_add ret (BV 64 0))
      (BV 64 18446744073709551614)) (BV 64 0)) (BV 64 1)).

Lemma return_word_fault_refuted (frame : SavedFrame) :
  bv_unsigned (savedReturnAddress frame) mod 4 = 0 ->
  exists Q, SimplImpl (bv_extract 0 1 (bv_shiftr
    (bv_or (bv_and (bv_add (savedReturnAddress frame) (BV 64 0))
      (BV 64 18446744073709551614)) (BV 64 0)) (BV 64 1)) = BV 1 1) Q /\ Q = False.
Proof.
  intros Haligned. eexists. split; [zesu_return_integer_fault | reflexivity].
Qed.

(* The alignment inside a folded precondition. *)
Definition savedFrameWellFormed (frame : SavedFrame) : Prop :=
  0 < bv_unsigned (savedReturnAddress frame) /\
  bv_unsigned (savedReturnAddress frame) mod 4 = 0.

Lemma return_word_fault_folded (frame : SavedFrame) :
  savedFrameWellFormed frame ->
  exists Q, SimplImpl (bv_extract 0 1 (bv_shiftr
    (bv_or (bv_and (bv_add (savedReturnAddress frame) (BV 64 0))
      (BV 64 18446744073709551614)) (BV 64 0)) (BV 64 1)) = BV 1 1) Q /\ Q = False.
Proof.
  intros Hwf. eexists. split; [zesu_return_integer_fault | reflexivity].
Qed.

(* No alignment fact: the arm is not refuted. *)
Lemma return_word_fault_unaligned (frame : SavedFrame) : True.
Proof.
  Fail assert (exists Q, SimplImpl (bv_extract 0 1 (bv_shiftr
    (bv_or (bv_and (bv_add (savedReturnAddress frame) (BV 64 0))
      (BV 64 18446744073709551614)) (BV 64 0)) (BV 64 1)) = BV 1 1) Q)
    by (eexists; zesu_return_integer_fault).
  exact I.
Qed.

(* The integer form keeps its own branch. *)
Lemma return_integer_fault_refuted (R : Z) :
  0 <= R -> R < 2 ^ 64 -> R mod 4 = 0 ->
  exists Q, SimplImpl (bv_extract 0 1 (bv_shiftr
    (bv_or (bv_and (bv_add (Z_to_bv 64 R) (BV 64 0))
      (BV 64 18446744073709551614)) (BV 64 0)) (BV 64 1)) = BV 1 1) Q /\ Q = False.
Proof.
  intros Hlower Hupper Haligned. eexists. split; [zesu_return_integer_fault | reflexivity].
Qed.
