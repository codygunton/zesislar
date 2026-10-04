(* Generic bit-vector facts, moved from the writeSuccess proof tree. *)
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.

Import ListNotations.

Lemma bv_sign_extend_64_idemp (b : bv 64) : bv_sign_extend 64 b = b.
Proof. apply bv_sign_extend_idemp. Qed.

Lemma bv_zero_extend_64_zero_8 (b : bv 8) :
  bv_zero_extend 64 b = BV 64 0 -> b = BV 8 0.
Proof.
  move => Hzero.
  apply bv_eq.
  move: (f_equal bv_unsigned Hzero).
  rewrite bv_zero_extend_unsigned // !bv_unsigned_BV //.
Qed.

Lemma bv_unsigned_add_no_wrap_64 (left right : bv 64) :
  (bv_unsigned left + bv_unsigned right < 2 ^ 64)%Z ->
  bv_unsigned (left + right)%bv = bv_unsigned left + bv_unsigned right.
Proof.
  move => Hsum. rewrite bv_add_unsigned.
  apply bv_wrap_small.
  pose proof (bv_unsigned_in_range 64 left).
  pose proof (bv_unsigned_in_range 64 right).
  unfold bv_modulus in *. cbn in *. lia.
Qed.

(* Select this rule explicitly. Unselected proofs keep their search order. *)
Class ZesuStepSignedAddress : Prop := zesu_step_signed_address : True.

Lemma zesu_signed_zero_extend_64_128 (value : bv 64) :
  bv_signed (bv_zero_extend 128 value) = bv_unsigned value.
Proof. rewrite bv_zero_extend_signed bv_swrap_small; bv_solve. Qed.

Lemma zesu_signed_zero_extend_add_64_128
    (value : bv 64) (offset : bv 128) :
  bv_unsigned offset < 2 ^ 64 ->
  bv_signed (bv_zero_extend 128 value + offset) =
    bv_unsigned value + bv_unsigned offset.
Proof.
  move => Hoffset.
  rewrite bv_add_signed bv_zero_extend_signed.
  rewrite !bv_swrap_small; bv_solve.
Qed.
