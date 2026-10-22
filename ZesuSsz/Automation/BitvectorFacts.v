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

Class ZesuStepStrictSigned : Prop := zesu_step_strict_signed : True.

Lemma zesu_unsigned_lt_signed_zero_extend_64_128 (left right : bv 64) :
  bv_unsigned left < bv_unsigned right ->
  bv_signed (bv_zero_extend 128 left) <
    bv_signed (bv_zero_extend 128 right).
Proof. rewrite !zesu_signed_zero_extend_64_128. exact (fun Hlt => Hlt). Qed.

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

Lemma zesu_unsigned_add_signed_64 (left right : bv 64) :
  0 <= bv_unsigned left + bv_signed right < 2 ^ 64 ->
  bv_unsigned (left + right) = bv_unsigned left + bv_signed right.
Proof. move => Hsum. bv_solve. Qed.

Lemma zesu_unsigned_sub_no_wrap_64 (left right : bv 64) :
  bv_unsigned right <= bv_unsigned left ->
  bv_unsigned (left - right) = bv_unsigned left - bv_unsigned right.
Proof. move => Hsub. rewrite bv_sub_unsigned bv_wrap_small; bv_solve. Qed.

Class ZesuStepLowMask : Prop := zesu_step_low_mask : True.

Class ZesuStepMaskNormalizer : Prop := zesu_step_mask_normalizer : True.

Lemma zesu_unsigned_low_mask_add (width low : N)
    (value offset mask : bv width) :
  (low <= width)%N ->
  bv_unsigned mask = Z.ones (Z.of_N low) ->
  bv_unsigned (bv_and (value + offset) mask) =
    bv_unsigned (Z_to_bv low (bv_unsigned value + bv_unsigned offset)).
Proof.
  intros Hwidth Hmask.
  rewrite bv_and_unsigned Hmask -bv_wrap_land bv_add_unsigned Z_to_bv_unsigned.
  apply bv_wrap_bv_wrap. exact Hwidth.
Qed.

Lemma zesu_unsigned_low_mask_add_integer (width low : N)
    (value mask : bv width) (offset : Z) :
  (low <= width)%N ->
  bv_unsigned mask = Z.ones (Z.of_N low) ->
  bv_unsigned (bv_and (value + Z_to_bv width offset) mask) =
    bv_unsigned (Z_to_bv low (bv_unsigned value + offset)).
Proof.
  intros Hwidth Hmask.
  rewrite bv_and_unsigned Hmask -bv_wrap_land bv_add_unsigned !Z_to_bv_unsigned.
  rewrite (bv_wrap_bv_wrap low width _ Hwidth).
  rewrite -(bv_wrap_add_idemp_r low (bv_unsigned value) (bv_wrap width offset)).
  rewrite (bv_wrap_bv_wrap low width _ Hwidth).
  apply bv_wrap_add_idemp_r.
Qed.

Lemma zesu_unsigned_low_mask_add_sub_modulus (width low : N)
    (value mask : bv width) (offset : Z) :
  (low <= width)%N ->
  bv_unsigned mask = Z.ones (Z.of_N low) ->
  bv_modulus low <= bv_unsigned value + offset < 2 * bv_modulus low ->
  bv_unsigned (bv_and (value + Z_to_bv width offset) mask) =
    bv_unsigned value + offset - bv_modulus low.
Proof.
  intros Hwidth Hmask Hrange.
  rewrite (zesu_unsigned_low_mask_add_integer width low value mask offset Hwidth Hmask).
  rewrite Z_to_bv_unsigned.
  rewrite -(bv_wrap_sub_modulus_1 low (bv_unsigned value + offset)).
  apply bv_wrap_small. lia.
Qed.


Lemma zesu_low_mask_add_bv_sub_modulus (width low : N)
    (value mask : bv width) (offset : Z) :
  (low <= width)%N ->
  bv_unsigned mask = Z.ones (Z.of_N low) ->
  bv_modulus low <= bv_unsigned value + offset < 2 * bv_modulus low ->
  bv_and (value + Z_to_bv width offset) mask =
    Z_to_bv width (bv_unsigned value + offset - bv_modulus low).
Proof.
  intros Hwidth Hmask Hrange.
  apply bv_eq. rewrite bv_and_unsigned Z_to_bv_unsigned.
  pose proof (zesu_unsigned_low_mask_add_sub_modulus
    width low value mask offset Hwidth Hmask Hrange) as Hunsigned.
  rewrite bv_and_unsigned in Hunsigned. rewrite Hunsigned.
  symmetry. apply bv_wrap_small.
  pose proof (bv_modulus_le_mono low width Hwidth). lia.
Qed.

(* Normalize supported branch conditions before general arithmetic. *)
Class ZesuStepBranchGuards : Prop := zesu_step_branch_guards : True.

Local Open Scope Z_scope.
Lemma zesu_guard_low_mask_one_wrap (width low : N) (value mask : bv width) :
  (low <= width)%N ->
  bv_unsigned mask = Z.ones (Z.of_N low) ->
  bv_modulus low <= bv_unsigned value < 2 * bv_modulus low ->
  bv_unsigned (bv_and value mask) = bv_unsigned value - bv_modulus low.
Proof.
  intros Hwidth Hmask Hrange.
  rewrite bv_and_unsigned Hmask.
  rewrite <- (bv_wrap_land low (bv_unsigned value)).
  rewrite <- (bv_wrap_sub_modulus_1 low (bv_unsigned value)).
  apply bv_wrap_small. lia.
Qed.

Lemma zesu_guard_mask_signed_value (width low : N) (value : bv low) (mask : bv width) :
  (low <= width)%N ->
  bv_unsigned mask = Z.ones (Z.of_N low) ->
  bv_unsigned (bv_and (Z_to_bv width (bv_signed value)) mask) = bv_unsigned value.
Proof.
  intros Hwidth Hmask.
  rewrite bv_and_unsigned Hmask.
  rewrite <- (bv_wrap_land low (bv_unsigned (Z_to_bv width (bv_signed value)))).
  rewrite Z_to_bv_unsigned bv_wrap_bv_wrap; last exact Hwidth.
  unfold bv_signed, bv_swrap. rewrite bv_wrap_sub_idemp_l.
  replace (bv_unsigned value + bv_half_modulus low - bv_half_modulus low)
    with (bv_unsigned value) by ring.
  apply bv_wrap_bv_unsigned.
Qed.

Lemma zesu_guard_signed_negative (width : N) (value : bv width) :
  width <> 0%N ->
  (bv_signed value < 0 <-> bv_half_modulus width <= bv_unsigned value).
Proof.
  intro Hwidth.
  pose proof (bv_unsigned_in_range width value) as Hrange.
  pose proof (bv_half_modulus_nonneg width) as Hhalf.
  pose proof (bv_half_modulus_twice width Hwidth) as Hmodulus.
  unfold bv_signed, bv_swrap.
  destruct (Z_le_gt_dec (bv_half_modulus width) (bv_unsigned value)).
  - rewrite <- (bv_wrap_sub_modulus_1 width
      (bv_unsigned value + bv_half_modulus width)).
    rewrite bv_wrap_small; lia.
  - rewrite bv_wrap_small; lia.
Qed.


Lemma zesu_guard_bv_eq_iff (width : N) (left right : bv width) :
  left = right <-> bv_unsigned left = bv_unsigned right.
Proof. split; [apply f_equal | apply bv_eq]. Qed.
