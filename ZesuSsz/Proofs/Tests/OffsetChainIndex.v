From Coq Require Import ZArith.ZArith Lists.List.
From stdpp.bitvector Require Import definitions.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Automation2.All.

(* A list index measured from a closed-offset chain on a word, against a base
   on the same word, is a literal once the word's range facts rule out a wrap.
   The facts sit folded in a predicate over the record the word is read from. *)
Record OffsetFrame := { offsetPointer : bv 64 }.
Definition offsetFrameWellFormed (frame : OffsetFrame) : Prop :=
  (4096 <= bv_unsigned (offsetPointer frame))%Z /\
  (bv_unsigned (offsetPointer frame) < 4294967296)%Z.

(* A byte lookup at w - 400 + 400 - 376 in an array at w - 392. *)
Goal forall frame (bytes : list (bv 8)) value, offsetFrameWellFormed frame ->
  bytes !! Z.to_nat ((bv_unsigned (offsetPointer frame + BV 64 18446744073709551216 +
    BV 64 400 + BV 64 18446744073709551240) -
    (bv_unsigned (offsetPointer frame) - 400 + 8)) `div` 1) = Some value ->
  bytes !! 16%nat = Some value.
Proof.
  intros frame bytes value Hframe Hlookup.
  ZesuSsz.Automation2.WrappedWord.zesu_wrapped_index_step.
  exact Hlookup.
Qed.

(* A window read at w - 360 in the same array. *)
Goal forall frame (bytes : list (bv 8)) (P : list (bv 8) -> Prop),
  offsetFrameWellFormed frame -> P (take 2 (drop 32 bytes)) ->
  P (take 2 (drop (Z.to_nat (bv_unsigned (offsetPointer frame + BV 64 18446744073709551216 +
    BV 64 400 + BV 64 18446744073709551256) -
    (bv_unsigned (offsetPointer frame) - 400 + 8))) bytes)).
Proof.
  intros frame bytes P Hframe HP.
  ZesuSsz.Automation2.WrappedWord.zesu_wrapped_index_step.
  exact HP.
Qed.

(* Without the lower bound the address may wrap: no rewrite. *)
Goal forall frame (bytes : list (bv 8)) value,
  bytes !! Z.to_nat ((bv_unsigned (offsetPointer frame + BV 64 18446744073709551216 +
    BV 64 400 + BV 64 18446744073709551240) -
    (bv_unsigned (offsetPointer frame) - 400 + 8)) `div` 1) = Some value -> True.
Proof.
  intros frame bytes value Hlookup.
  Fail ZesuSsz.Automation2.WrappedWord.zesu_wrapped_index_step.
  exact I.
Qed.

(* A base on another word leaves the index symbolic: no rewrite. *)
Goal forall frame (other : bv 64) (bytes : list (bv 8)) value, offsetFrameWellFormed frame ->
  bytes !! Z.to_nat ((bv_unsigned (offsetPointer frame + BV 64 18446744073709551216 +
    BV 64 400 + BV 64 18446744073709551240) -
    (bv_unsigned other - 400 + 8)) `div` 1) = Some value -> True.
Proof.
  intros frame other bytes value Hframe Hlookup.
  Fail ZesuSsz.Automation2.WrappedWord.zesu_wrapped_index_step.
  exact I.
Qed.
