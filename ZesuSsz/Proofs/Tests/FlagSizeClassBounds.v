Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith NArith.NArith.
Require Import stdpp.bitvector.definitions.
Require Import ZesuSsz.Automation2.All.
Local Open Scope Z_scope.

(* A signed-comparison flag is a one-bit value under zero extension. A size
   class built from it by a subtraction stays above a masked argument minus
   a constant, which the code computes as a wrapped addition. *)
Lemma flag_size_class_sub (a b x : bv 64) :
  128 <= bv_unsigned (bv_and x (BV 64 255)) ->
  bv_unsigned (bv_and x (BV 64 255)) < 128 + 55 ->
  bv_unsigned (bv_add (bv_and x (BV 64 255)) (BV 64 (2^64 - 128))) <
    bv_unsigned (bv_sub (BV 64 56)
      (bv_zero_extend 64 (ite (bool_decide (bv_signed a < bv_signed b)) (BV 1 1) (BV 1 0)))).
Proof. intros. zesu_block2. Qed.

(* The size class is the flag xor 1, and a comparison fact fixes the flag. *)
Lemma flag_size_class_xor (a b x : bv 64) :
  bv_signed b <= bv_signed a ->
  bv_unsigned (bv_and x (BV 64 255)) = 128 ->
  bv_unsigned (bv_add (bv_and x (BV 64 255)) (BV 64 (2^64 - 128))) <
    bv_unsigned (bv_xor
      (bv_zero_extend 64 (ite (bool_decide (bv_signed a < bv_signed b)) (BV 1 1) (BV 1 0)))
      (BV 64 1)).
Proof. intros. zesu_block2. Qed.

(* The flag and the size class are local definitions. *)
Lemma flag_size_class_local (a b x : bv 64) :
  let flag := bv_zero_extend 64 (ite (bool_decide (bv_signed a < bv_signed b)) (BV 1 1) (BV 1 0)) in
  let size := bv_sub (BV 64 56) flag in
  128 <= bv_unsigned (bv_and x (BV 64 255)) ->
  bv_unsigned (bv_and x (BV 64 255)) < 128 + 55 ->
  bv_unsigned (bv_add (bv_and x (BV 64 255)) (BV 64 (2^64 - 128))) < bv_unsigned size.
Proof. intros. zesu_block2. Qed.

(* A lower bound on a low-bit mask of a 64-bit cast, from a range of the
   cast's source. *)
Lemma masked_cast_lower_bound (z : Z) :
  128 <= z -> z < 256 ->
  128 <= bv_unsigned (bv_and (Z_to_bv 64 z) (BV 64 255)).
Proof. intros. zesu_block2. Qed.

(* The cast is a zero extension of a byte. *)
Lemma masked_extension_lower_bound (y : bv 8) :
  128 <= bv_unsigned y ->
  128 <= bv_unsigned (bv_and (bv_zero_extend 64 y) (BV 64 255)).
Proof. intros. zesu_block2. Qed.
