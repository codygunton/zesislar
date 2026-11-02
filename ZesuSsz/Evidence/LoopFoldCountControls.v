Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.BitvectorFacts.
Require Import ZesuSsz.Automation.ByteMaskCast.
Require Import ZesuSsz.Automation.MaskWrapPresentation.
From Coq Require Import ZArith.ZArith Bool.Bool Lia.
From stdpp Require Import bitvector.definitions bitvector.tactics decidable.
Open Scope Z_scope.

Lemma loop_count_6a24 (byte : bv 8) :
  bool_decide (bv_signed (BV 128 183) < bv_signed (bv_zero_extend 128 (bv_and (bv_sign_extend 64 byte) (BV 64 255)))) = true ->
  negb (bool_decide (bv_signed (bv_zero_extend 128 (bv_and (bv_sign_extend 64 byte) (BV 64 255))) >= bv_signed (BV 128 192))) = true ->
  1 <= bv_unsigned (bv_and (bv_add (bv_and (bv_sign_extend 64 byte) (BV 64 255)) (BV 64 73)) (BV 64 255)) <= 8.
Proof.
  intros Hlower Hupper.
  pose proof (zesu_sign_extended_byte_mask 64 byte ltac:(lia)) as Hmask.
  assert (HclosedMask : BV 64 255 = Z_to_bv 64 (2 ^ 8 - 1))
    by (apply bv_eq; vm_compute; reflexivity).
  rewrite <- HclosedMask in Hmask.
  rewrite Hmask in *.
  pose proof (bv_unsigned_in_range 8 byte) as Hbyte.
  change (0 <= bv_unsigned byte < 256) in Hbyte.
  assert (Hcast : bv_unsigned (Z_to_bv 64 (bv_unsigned byte)) = bv_unsigned byte).
  { apply Z_to_bv_small. change (0 <= bv_unsigned byte < 18446744073709551616). lia. }
  apply bool_decide_eq_true_1 in Hlower.
  apply Bool.negb_true_iff in Hupper. apply bool_decide_eq_false_1 in Hupper.
  rewrite zesu_signed_zero_extend_64_128 in Hlower.
  rewrite zesu_signed_zero_extend_64_128 in Hupper.
  change (183 < bv_unsigned (Z_to_bv 64 (bv_unsigned byte))) in Hlower.
  change (~ (bv_unsigned (Z_to_bv 64 (bv_unsigned byte)) >= 192)) in Hupper.
  rewrite Hcast in Hlower. rewrite Hcast in Hupper.
  assert (HclosedBias : BV 64 73 = Z_to_bv 64 73)
    by (apply bv_eq; vm_compute; reflexivity).
  rewrite HclosedBias.
  rewrite (zesu_unsigned_low_mask_add_sub_modulus 64 8
    (Z_to_bv 64 (bv_unsigned byte)) (BV 64 255) 73 ltac:(lia) ltac:(reflexivity)
    ltac:(rewrite Hcast; change (256 <= bv_unsigned byte + 73 < 512); lia)).
  rewrite Hcast. change (1 <= bv_unsigned byte + 73 - 256 <= 8). lia.
Qed.

Lemma loop_count_6ac4 (byte : bv 8) :
  bool_decide (bv_signed (bv_zero_extend 128 (bv_and (bv_sign_extend 64 byte) (BV 64 255))) >= bv_signed (BV 128 248)) = true ->
  1 <= bv_unsigned (bv_and (bv_add (bv_and (bv_sign_extend 64 byte) (BV 64 255)) (BV 64 9)) (BV 64 255)) <= 8.
Proof.
  intros Hlower.
  pose proof (zesu_sign_extended_byte_mask 64 byte ltac:(lia)) as Hmask.
  assert (HclosedMask : BV 64 255 = Z_to_bv 64 (2 ^ 8 - 1))
    by (apply bv_eq; vm_compute; reflexivity).
  rewrite <- HclosedMask in Hmask.
  rewrite Hmask in *.
  pose proof (bv_unsigned_in_range 8 byte) as Hbyte.
  change (0 <= bv_unsigned byte < 256) in Hbyte.
  assert (Hcast : bv_unsigned (Z_to_bv 64 (bv_unsigned byte)) = bv_unsigned byte).
  { apply Z_to_bv_small. change (0 <= bv_unsigned byte < 18446744073709551616). lia. }
  apply bool_decide_eq_true_1 in Hlower.
  rewrite zesu_signed_zero_extend_64_128 in Hlower.
  change (bv_unsigned (Z_to_bv 64 (bv_unsigned byte)) >= 248) in Hlower.
  rewrite Hcast in Hlower.
  assert (HclosedBias : BV 64 9 = Z_to_bv 64 9)
    by (apply bv_eq; vm_compute; reflexivity).
  rewrite HclosedBias.
  rewrite (zesu_unsigned_low_mask_add_sub_modulus 64 8
    (Z_to_bv 64 (bv_unsigned byte)) (BV 64 255) 9 ltac:(lia) ltac:(reflexivity)
    ltac:(rewrite Hcast; change (256 <= bv_unsigned byte + 9 < 512); lia)).
  rewrite Hcast. change (1 <= bv_unsigned byte + 9 - 256 <= 8). lia.
Qed.

