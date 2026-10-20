Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.RlpDecodeItem.
Require Import ZesuSsz.Contracts.DecodeItemFrameImage.
Require Import ZesuSsz.Contracts.AbiBytes.
Require Import ZesuSsz.Contracts.ResultImage.
Require Import ZesuSsz.Contracts.RlpDecodeItemReturnImages.
From Coq Require Import List ZArith Lia.
Import ListNotations.
Open Scope Z_scope.

Lemma decodeItemStoredWordBytes (value : bv 64) :
  bv_to_little_endian 8 8 (bv_unsigned value) = word64Bytes (bv_unsigned value).
Proof.
  unfold word64Bytes, bv_to_little_endian, Z_to_little_endian.
  cbn [List.seq List.map Z.iter]. cbn.
  rewrite !Z.shiftr_shiftr; try lia.
  cbn. rewrite Z.shiftr_0_r. rewrite !Z.land_ones; try lia.
  repeat apply f_equal2; try reflexivity; apply bv_eq;
    rewrite !Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; cbn;
    rewrite Z.mod_mod; try reflexivity; lia.
Qed.

Lemma decodeItemStoredWordValue (value : bv 64) :
  littleEndian (bv_to_little_endian 8 8 (bv_unsigned value)) = bv_unsigned value.
Proof.
  apply (littleEndian_machine_bytes 8%nat).
  change (8 * Z.of_nat 8) with 64.
  pose proof (bv_unsigned_in_range 64 value) as Hrange.
  unfold bv_modulus in Hrange. exact Hrange.
Qed.

Lemma decodeItemStoredPointerImage (pointer lengthValue : bv 64) (tail : list byte) :
  fieldImage (bv_to_little_endian 8 8 (bv_unsigned pointer) ++
    bv_to_little_endian 8 8 (bv_unsigned lengthValue) ++ tail) 0
    (bv_to_little_endian 8 8 (bv_unsigned pointer)).
Proof.
  change (fieldImage (([] : list byte) ++
    bv_to_little_endian 8 8 (bv_unsigned pointer) ++
    (bv_to_little_endian 8 8 (bv_unsigned lengthValue) ++ tail))
    (length ([] : list byte)) (bv_to_little_endian 8 8 (bv_unsigned pointer))).
  apply fieldImage_middle.
Qed.

Lemma decodeItemStoredLengthImage (pointer lengthValue : bv 64) (tail : list byte) :
  fieldImage (bv_to_little_endian 8 8 (bv_unsigned pointer) ++
    bv_to_little_endian 8 8 (bv_unsigned lengthValue) ++ tail) 8
    (bv_to_little_endian 8 8 (bv_unsigned lengthValue)).
Proof.
  replace 8%nat with (length (bv_to_little_endian 8 8 (bv_unsigned pointer))) by
    (rewrite length_bv_to_little_endian; lia).
  apply fieldImage_middle.
Qed.


Print Assumptions decodeItemStoredWordBytes.
Print Assumptions decodeItemStoredWordValue.
Print Assumptions decodeItemStoredPointerImage.
Print Assumptions decodeItemStoredLengthImage.

#[export] Hint Extern 1
  (SimplAnd (fieldImage (bv_to_little_endian 8 8 (bv_unsigned ?pointer) ++
    bv_to_little_endian 8 8 (bv_unsigned ?lengthValue) ++ ?tail) 0
    (word64Bytes (bv_unsigned ?pointer))) True) =>
  unfold SimplAnd; split;
  [intros _; rewrite <- decodeItemStoredWordBytes; apply decodeItemStoredPointerImage
  | intros _; exact I] : typeclass_instances.

#[export] Hint Extern 1
  (SimplAnd (fieldImage (bv_to_little_endian 8 8 (bv_unsigned ?pointer) ++
    bv_to_little_endian 8 8 (bv_unsigned ?lengthValue) ++ ?tail) 8
    (word64Bytes (bv_unsigned ?lengthValue))) True) =>
  unfold SimplAnd; split;
  [intros _; rewrite <- decodeItemStoredWordBytes; apply decodeItemStoredLengthImage
  | intros _; exact I] : typeclass_instances.
