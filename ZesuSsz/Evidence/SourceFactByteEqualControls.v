Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.SourceFactByteViews.
From Coq Require Import ZArith NArith.
From stdpp Require Import bitvector.tactics.
Require Import ZesuSsz.Automation.All.
Local Open Scope Z_scope.

Lemma byte_equal64 : forall byte : bv 8,
  bv_and (bv_sign_extend 64 byte) (BV 64 255) = BV 64 128 ->
  bv_unsigned byte = 128.
Proof. intros byte Hsource. SourceFactByteViews.zesu_source_byte_equal. Qed.

Lemma byte_equal16 : forall byte : bv 8,
  bv_and (bv_sign_extend 16 byte) (BV 16 255) = BV 16 37 ->
  bv_unsigned byte = 37.
Proof. intros byte Hsource. SourceFactByteViews.zesu_source_byte_equal. Qed.

Lemma byte_equal_projection : forall byte : bv 8,
  bv_and (bv_sign_extend 64 byte) (BV 64 255) = BV 64 128 ->
  bv_unsigned byte = 128 /\ 128 <= bv_unsigned byte /\ bv_unsigned byte <= 128.
Proof.
  intros byte Hsource. SourceFactByteViews.zesu_source_byte_views.
  repeat split; assumption.
Qed.

Lemma byte_equal_symbolic_mask_refuses : forall (byte : bv 8) (mask : bv 64),
  bv_and (bv_sign_extend 64 byte) mask = BV 64 128 -> True.
Proof.
  intros byte mask Hsource.
  tryif (assert (Hview : bv_unsigned byte = 128) by
    SourceFactByteViews.zesu_source_byte_equal)
  then fail 100 "The symbolic mask passed closed-term validation."
  else exact I.
Qed.

Lemma byte_equal_symbolic_value_refuses : forall (byte : bv 8) (value : Z),
  bv_and (bv_sign_extend 64 byte) (BV 64 255) = Z_to_bv 64 value -> True.
Proof.
  intros byte value Hsource.
  tryif (assert (Hview : bv_unsigned byte = value) by
    SourceFactByteViews.zesu_source_byte_equal)
  then fail 100 "The symbolic value passed closed-term validation."
  else exact I.
Qed.

Lemma byte_equal_small_width_refuses : forall byte : bv 8,
  bv_and (bv_sign_extend 4 byte) (BV 4 15) = BV 4 0 -> True.
Proof.
  intros byte Hsource.
  tryif (assert (Hview : bv_unsigned byte = 0) by
    SourceFactByteViews.zesu_source_byte_equal)
  then fail 100 "The unsupported width passed the bound criterion."
  else exact I.
Qed.

Lemma byte_equal_changed_result_refuses : forall byte : bv 8,
  bv_and (bv_sign_extend 64 byte) (BV 64 255) = BV 64 129 -> True.
Proof.
  intros byte Hsource.
  tryif (assert (Hview : bv_unsigned byte = 128) by
    SourceFactByteViews.zesu_source_byte_equal)
  then fail 100 "The changed result passed the source comparison."
  else exact I.
Qed.
