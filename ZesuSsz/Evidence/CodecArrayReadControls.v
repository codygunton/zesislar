(* Generic controls only. This file states no caller-boundary theorem. *)
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Automation.CodecArrayRead.
From stdpp Require Import bitvector.definitions list.
From Coq Require Import Lists.List ZArith.ZArith Lia.
Local Open Scope Z_scope.

Section image_controls.
Context (enabled : ZesuStepCodecArrayRead).

Lemma codec_read_suffix_image (base : Z) (a b : bv 8)
    (word decoded : bv 16)
    (image : decoded = Z_to_bv 16 (little_endian_to_bv 8
      (take 2 (drop (Z.to_nat (base + 2 - base))
        (a :: b :: bv_to_little_endian 2 8 (bv_unsigned word)))))) :
    decoded = word.
Proof.
  zesu_codec_array_read_image image.
  exact image.
Qed.

Lemma codec_read_partial_slice (a b : bv 8) (word decoded : bv 16)
    (image : decoded = Z_to_bv 16 (little_endian_to_bv 8
      (take 1 (drop (Z.to_nat 2)
        (a :: b :: bv_to_little_endian 2 8 (bv_unsigned word)))))) : True.
Proof.
  Fail zesu_codec_array_read_image image.
  exact I.
Qed.

Lemma codec_read_wrong_offset (a b : bv 8) (word decoded : bv 16)
    (image : decoded = Z_to_bv 16 (little_endian_to_bv 8
      (take 2 (drop (Z.to_nat 1)
        (a :: b :: bv_to_little_endian 2 8 (bv_unsigned word)))))) : True.
Proof.
  Fail zesu_codec_array_read_image image.
  exact I.
Qed.

Lemma codec_read_changed_image (a b : bv 8) (word decoded : bv 16)
    (image : decoded = Z_to_bv 16 (little_endian_to_bv 8
      (take 2 (drop (Z.to_nat 2)
        (a :: b :: bv_to_little_endian 2 8 (bv_unsigned word + 1)))))) : True.
Proof.
  Fail zesu_codec_array_read_image image.
  exact I.
Qed.

Lemma codec_read_symbolic_count (digits : Z) (a b : bv 8)
    (word decoded : bv 16)
    (image : decoded = Z_to_bv 16 (little_endian_to_bv 8
      (take 2 (drop (Z.to_nat 2)
        (a :: b :: bv_to_little_endian digits 8 (bv_unsigned word)))))) : True.
Proof.
  Fail zesu_codec_array_read_image image.
  exact I.
Qed.

Lemma codec_read_wrong_result_width (a b : bv 8)
    (word : bv 16) (decoded : bv 8)
    (image : decoded = Z_to_bv 8 (little_endian_to_bv 8
      (take 2 (drop (Z.to_nat 2)
        (a :: b :: bv_to_little_endian 2 8 (bv_unsigned word)))))) : True.
Proof.
  Fail zesu_codec_array_read_image image.
  exact I.
Qed.
End image_controls.

Lemma codec_read_disabled (a b : bv 8) (word decoded : bv 16)
    (image : decoded = Z_to_bv 16 (little_endian_to_bv 8
      (take 2 (drop (Z.to_nat 2)
        (a :: b :: bv_to_little_endian 2 8 (bv_unsigned word)))))) : True.
Proof.
  Fail zesu_codec_array_read_image image.
  exact I.
Qed.

Lemma codec_read_wrong_shape : True.
Proof.
  assert (enabled : ZesuStepCodecArrayRead) by constructor.
  Fail zesu_codec_array_read.
  exact I.
Qed.

Section continuation_controls.
Context `{!islaG Sigma} `{!threadG}.

Lemma codec_read_preserves_owner (enabled : ZesuStepCodecArrayRead)
    (base : Z) (fraction : dfrac) (a b : bv 8)
    (word loaded : bv 16) (K : iProp Sigma) :
  K -∗
  ∀ value : bv 16,
    ⌜value = Z_to_bv 16 (little_endian_to_bv 8
      (take 2 (drop (Z.to_nat (base + 2 - base))
        (a :: b :: bv_to_little_endian 2 8 (bv_unsigned word)))))⌝ -∗
    ⌜loaded = value⌝ -∗
    base ↦ₘ{fraction}∗ (a :: b :: bv_to_little_endian 2 8 (bv_unsigned word)) -∗
    base ↦ₘ{fraction}∗ (a :: b :: bv_to_little_endian 2 8 (bv_unsigned word)) ∗ K.
Proof.
  iIntros "HK".
  zesu_codec_array_read_consumer.
  iFrame.
Qed.
End continuation_controls.
