Require Import ZesuSsz.Automation.All.
From Coq Require Import List Lia ZArith.
From stdpp Require Import bitvector.definitions.
Require Import SailStdpp.MachineWord EvmSailRlp.evm_rlp_types.
Require Import ZesuSsz.Contracts.ResultImage.
Require Import ZesuSsz.Contracts.RlpDecodeItem.
Require Import ZesuSsz.Contracts.RlpDecodeItemSchema.
Import ListNotations.
Open Scope Z_scope.

(* The five success returns write four fields and preserve two gaps.
   This list is the complete selected 40-byte Ok image, parameterized by
   the three stored eight-byte words and the caller's padding bytes. *)
Definition decodeItemOkBytes (before pointerBytes lengthBytes consumedBytes : list byte)
    (isList : bool) : list byte :=
  pointerBytes ++ lengthBytes ++ [Z_to_bv 8 (if isList then 1 else 0)] ++
  firstn 7 (skipn 17 before) ++ consumedBytes ++
  [Z_to_bv 8 0; Z_to_bv 8 0] ++ firstn 6 (skipn 34 before).

Lemma fieldImage_middle prefix field suffix :
  fieldImage (prefix ++ field ++ suffix) (length prefix) field.
Proof.
  intros i Hi.
  rewrite nth_error_app2 by lia.
  replace (length prefix + i - length prefix)%nat with i by lia.
  rewrite nth_error_app1 by lia.
  reflexivity.
Qed.

Lemma selectedPadLength (before : list byte) offset count :
  (length before = 40)%nat ->
  (offset + count <= 40)%nat ->
  (length (firstn count (skipn offset before)) = count)%nat.
Proof.
  intros Hbefore Hrange.
  rewrite firstn_length, skipn_length, Hbefore.
  lia.
Qed.

Lemma decodeItemOkBytes_length before pointerBytes lengthBytes consumedBytes isList :
  (length before = 40)%nat ->
  (length pointerBytes = 8)%nat ->
  (length lengthBytes = 8)%nat ->
  (length consumedBytes = 8)%nat ->
  (length (decodeItemOkBytes before pointerBytes lengthBytes consumedBytes isList) = 40)%nat.
Proof.
  intros Hbefore Hp Hl Hc.
  unfold decodeItemOkBytes.
  repeat rewrite app_length.
  rewrite (selectedPadLength before 17 7),
          (selectedPadLength before 34 6) by lia.
  simpl. lia.
Qed.

Lemma decodeItemOkBytes_pointer before pointerBytes lengthBytes consumedBytes isList :
  fieldImage (decodeItemOkBytes before pointerBytes lengthBytes consumedBytes isList)
    0 pointerBytes.
Proof.
  unfold decodeItemOkBytes.
  change (fieldImage (([] : list byte) ++ pointerBytes ++
    (lengthBytes ++ [Z_to_bv 8 (if isList then 1 else 0)] ++
     firstn 7 (skipn 17 before) ++ consumedBytes ++
     [Z_to_bv 8 0; Z_to_bv 8 0] ++ firstn 6 (skipn 34 before)))
    (length ([] : list byte)) pointerBytes).
  apply fieldImage_middle.
Qed.

Lemma decodeItemOkBytes_length_field before pointerBytes lengthBytes consumedBytes isList :
  (length pointerBytes = 8)%nat ->
  fieldImage (decodeItemOkBytes before pointerBytes lengthBytes consumedBytes isList)
    8 lengthBytes.
Proof.
  intro Hp.
  unfold decodeItemOkBytes.
  replace (pointerBytes ++ lengthBytes ++
      [Z_to_bv 8 (if isList then 1 else 0)] ++
      firstn 7 (skipn 17 before) ++ consumedBytes ++
      [Z_to_bv 8 0; Z_to_bv 8 0] ++ firstn 6 (skipn 34 before))
    with (pointerBytes ++ lengthBytes ++
      ([Z_to_bv 8 (if isList then 1 else 0)] ++
       firstn 7 (skipn 17 before) ++ consumedBytes ++
       [Z_to_bv 8 0; Z_to_bv 8 0] ++ firstn 6 (skipn 34 before)))
    by (repeat rewrite app_assoc; reflexivity).
  rewrite <- Hp.
  apply fieldImage_middle.
Qed.

Lemma decodeItemOkBytes_consumed_field before pointerBytes lengthBytes consumedBytes isList :
  (length before = 40)%nat ->
  (length pointerBytes = 8)%nat ->
  (length lengthBytes = 8)%nat ->
  fieldImage (decodeItemOkBytes before pointerBytes lengthBytes consumedBytes isList)
    24 consumedBytes.
Proof.
  intros Hbefore Hp Hl.
  unfold decodeItemOkBytes.
  set (prefix := pointerBytes ++ lengthBytes ++
    [Z_to_bv 8 (if isList then 1 else 0)] ++
    firstn 7 (skipn 17 before)).
  replace (pointerBytes ++ lengthBytes ++
      [Z_to_bv 8 (if isList then 1 else 0)] ++
      firstn 7 (skipn 17 before) ++ consumedBytes ++
      [Z_to_bv 8 0; Z_to_bv 8 0] ++ firstn 6 (skipn 34 before))
    with (prefix ++ consumedBytes ++
      ([Z_to_bv 8 0; Z_to_bv 8 0] ++ firstn 6 (skipn 34 before)))
    by (unfold prefix; repeat rewrite app_assoc; reflexivity).
  replace 24%nat with (length prefix).
  - apply fieldImage_middle.
  - unfold prefix. repeat rewrite app_length.
    rewrite Hp, Hl, (selectedPadLength before 17 7) by lia.
    simpl. lia.
Qed.

Lemma preservedImage_of_slice before after offset count :
  (length before = 40)%nat ->
  (offset + count <= 40)%nat ->
  fieldImage after offset (firstn count (skipn offset before)) ->
  preservedImage before after offset count.
Proof.
  intros Hbefore Hrange Hfield i Hi.
  assert (Hpad : (i < length (firstn count (skipn offset before)))%nat).
  { rewrite (selectedPadLength before offset count); lia. }
  specialize (Hfield i Hpad).
  rewrite nth_error_firstn_inside in Hfield by exact Hi.
  rewrite nth_error_skipn_offset in Hfield.
  exact Hfield.
Qed.

Lemma decodeItemOkBytes_flag_field before pointerBytes lengthBytes consumedBytes isList :
  (length pointerBytes = 8)%nat ->
  (length lengthBytes = 8)%nat ->
  fieldImage (decodeItemOkBytes before pointerBytes lengthBytes consumedBytes isList)
    16 [Z_to_bv 8 (if isList then 1 else 0)].
Proof.
  intros Hp Hl.
  unfold decodeItemOkBytes.
  replace (pointerBytes ++ lengthBytes ++
      [Z_to_bv 8 (if isList then 1 else 0)] ++
      firstn 7 (skipn 17 before) ++ consumedBytes ++
      [Z_to_bv 8 0; Z_to_bv 8 0] ++ firstn 6 (skipn 34 before))
    with ((pointerBytes ++ lengthBytes) ++
      [Z_to_bv 8 (if isList then 1 else 0)] ++
      (firstn 7 (skipn 17 before) ++ consumedBytes ++
       [Z_to_bv 8 0; Z_to_bv 8 0] ++ firstn 6 (skipn 34 before)))
    by (repeat rewrite app_assoc; reflexivity).
  replace 16%nat with (length (pointerBytes ++ lengthBytes)).
  - apply fieldImage_middle.
  - rewrite app_length, Hp, Hl. lia.
Qed.

Lemma decodeItemOkBytes_pad17_field before pointerBytes lengthBytes consumedBytes isList :
  (length pointerBytes = 8)%nat ->
  (length lengthBytes = 8)%nat ->
  fieldImage (decodeItemOkBytes before pointerBytes lengthBytes consumedBytes isList)
    17 (firstn 7 (skipn 17 before)).
Proof.
  intros Hp Hl.
  unfold decodeItemOkBytes.
  replace (pointerBytes ++ lengthBytes ++
      [Z_to_bv 8 (if isList then 1 else 0)] ++
      firstn 7 (skipn 17 before) ++ consumedBytes ++
      [Z_to_bv 8 0; Z_to_bv 8 0] ++ firstn 6 (skipn 34 before))
    with ((pointerBytes ++ lengthBytes ++
      [Z_to_bv 8 (if isList then 1 else 0)]) ++
      firstn 7 (skipn 17 before) ++
      (consumedBytes ++ [Z_to_bv 8 0; Z_to_bv 8 0] ++
       firstn 6 (skipn 34 before)))
    by (repeat rewrite app_assoc; reflexivity).
  replace 17%nat with
    (length (pointerBytes ++ lengthBytes ++
      [Z_to_bv 8 (if isList then 1 else 0)])).
  - apply fieldImage_middle.
  - repeat rewrite app_length. rewrite Hp, Hl. simpl. lia.
Qed.

Lemma decodeItemOkBytes_status_field before pointerBytes lengthBytes consumedBytes isList :
  (length before = 40)%nat ->
  (length pointerBytes = 8)%nat ->
  (length lengthBytes = 8)%nat ->
  (length consumedBytes = 8)%nat ->
  fieldImage (decodeItemOkBytes before pointerBytes lengthBytes consumedBytes isList)
    32 [Z_to_bv 8 0; Z_to_bv 8 0].
Proof.
  intros Hbefore Hp Hl Hc.
  unfold decodeItemOkBytes.
  set (prefix := pointerBytes ++ lengthBytes ++
    [Z_to_bv 8 (if isList then 1 else 0)] ++
    firstn 7 (skipn 17 before) ++ consumedBytes).
  replace (pointerBytes ++ lengthBytes ++
      [Z_to_bv 8 (if isList then 1 else 0)] ++
      firstn 7 (skipn 17 before) ++ consumedBytes ++
      [Z_to_bv 8 0; Z_to_bv 8 0] ++ firstn 6 (skipn 34 before))
    with (prefix ++ [Z_to_bv 8 0; Z_to_bv 8 0] ++
      firstn 6 (skipn 34 before))
    by (unfold prefix; repeat rewrite app_assoc; reflexivity).
  replace 32%nat with (length prefix).
  - apply fieldImage_middle.
  - unfold prefix. repeat rewrite app_length.
    rewrite Hp, Hl, Hc, (selectedPadLength before 17 7) by lia.
    simpl. lia.
Qed.

Lemma decodeItemOkBytes_pad34_field before pointerBytes lengthBytes consumedBytes isList :
  (length before = 40)%nat ->
  (length pointerBytes = 8)%nat ->
  (length lengthBytes = 8)%nat ->
  (length consumedBytes = 8)%nat ->
  fieldImage (decodeItemOkBytes before pointerBytes lengthBytes consumedBytes isList)
    34 (firstn 6 (skipn 34 before)).
Proof.
  intros Hbefore Hp Hl Hc.
  unfold decodeItemOkBytes.
  replace (pointerBytes ++ lengthBytes ++
      [Z_to_bv 8 (if isList then 1 else 0)] ++
      firstn 7 (skipn 17 before) ++ consumedBytes ++
      [Z_to_bv 8 0; Z_to_bv 8 0] ++ firstn 6 (skipn 34 before))
    with ((pointerBytes ++ lengthBytes ++
      [Z_to_bv 8 (if isList then 1 else 0)] ++
      firstn 7 (skipn 17 before) ++ consumedBytes ++
      [Z_to_bv 8 0; Z_to_bv 8 0]) ++
      firstn 6 (skipn 34 before) ++ ([] : list byte))
    by (repeat rewrite app_assoc; rewrite app_nil_r; reflexivity).
  replace 34%nat with
    (length (pointerBytes ++ lengthBytes ++
      [Z_to_bv 8 (if isList then 1 else 0)] ++
      firstn 7 (skipn 17 before) ++ consumedBytes ++
      [Z_to_bv 8 0; Z_to_bv 8 0])).
  - apply fieldImage_middle.
  - repeat rewrite app_length.
    rewrite Hp, Hl, Hc, (selectedPadLength before 17 7) by lia.
    simpl. lia.
Qed.

Lemma byteAt_from_singleton_image after offset value :
  fieldImage after offset [Z_to_bv 8 value] ->
  bv_unsigned (Z_to_bv 8 value) = value ->
  byteAt after offset value.
Proof.
  intros Hfield Hvalue.
  specialize (Hfield 0%nat ltac:(simpl; lia)).
  replace (offset + 0)%nat with offset in Hfield by lia.
  unfold byteAt. rewrite Hfield. simpl. now rewrite Hvalue.
Qed.

Lemma decodeItemOkBytes_flag before pointerBytes lengthBytes consumedBytes isList :
  (length pointerBytes = 8)%nat ->
  (length lengthBytes = 8)%nat ->
  byteAt (decodeItemOkBytes before pointerBytes lengthBytes consumedBytes isList)
    16 (if isList then 1 else 0).
Proof.
  intros Hp Hl.
  apply byteAt_from_singleton_image.
  - apply decodeItemOkBytes_flag_field; assumption.
  - destruct isList; reflexivity.
Qed.

Lemma decodeItemOkBytes_status before pointerBytes lengthBytes consumedBytes isList :
  (length before = 40)%nat ->
  (length pointerBytes = 8)%nat ->
  (length lengthBytes = 8)%nat ->
  (length consumedBytes = 8)%nat ->
  byteAt (decodeItemOkBytes before pointerBytes lengthBytes consumedBytes isList)
    32 0 /\
  byteAt (decodeItemOkBytes before pointerBytes lengthBytes consumedBytes isList)
    33 0.
Proof.
  intros Hbefore Hp Hl Hc.
  pose proof (decodeItemOkBytes_status_field before pointerBytes lengthBytes
    consumedBytes isList Hbefore Hp Hl Hc) as Hfield.
  split; unfold byteAt.
  - specialize (Hfield 0%nat ltac:(simpl; lia)).
    replace (32 + 0)%nat with 32%nat in Hfield by lia.
    rewrite Hfield. reflexivity.
  - specialize (Hfield 1%nat ltac:(simpl; lia)).
    replace (32 + 1)%nat with 33%nat in Hfield by lia.
    rewrite Hfield. reflexivity.
Qed.

Lemma decodeItemOkBytes_success before pointerBytes lengthBytes consumedBytes
    payloadPointer payloadLength consumed isList :
  (length before = 40)%nat ->
  (length pointerBytes = 8)%nat ->
  (length lengthBytes = 8)%nat ->
  (length consumedBytes = 8)%nat ->
  littleEndian pointerBytes = payloadPointer ->
  littleEndian lengthBytes = payloadLength ->
  littleEndian consumedBytes = consumed ->
  successResult40 before
    (decodeItemOkBytes before pointerBytes lengthBytes consumedBytes isList)
    payloadPointer payloadLength isList consumed.
Proof.
  intros Hbefore Hp Hl Hc Hpv Hlv Hcv.
  apply (successResult40_from_images before
    (decodeItemOkBytes before pointerBytes lengthBytes consumedBytes isList)
    pointerBytes lengthBytes consumedBytes); try assumption.
  - apply decodeItemOkBytes_length; assumption.
  - apply decodeItemOkBytes_pointer.
  - apply decodeItemOkBytes_length_field; assumption.
  - apply decodeItemOkBytes_consumed_field; assumption.
  - apply decodeItemOkBytes_flag; assumption.
  - apply (decodeItemOkBytes_status before pointerBytes lengthBytes
      consumedBytes isList); assumption.
  - apply (decodeItemOkBytes_status before pointerBytes lengthBytes
      consumedBytes isList); assumption.
  - apply (preservedImage_of_slice before _ 17 7); try lia.
    apply decodeItemOkBytes_pad17_field; assumption.
  - apply (preservedImage_of_slice before _ 34 6); try lia.
    apply decodeItemOkBytes_pad34_field; assumption.
Qed.

Lemma decodeItemOkBytes_encodeSuccess inputPointer input before
    pointerBytes lengthBytes consumedBytes isList headerLength payloadLength :
  (length before = 40)%nat ->
  (length pointerBytes = 8)%nat ->
  (length lengthBytes = 8)%nat ->
  (length consumedBytes = 8)%nat ->
  littleEndian pointerBytes =
    itemPayloadPointer inputPointer input headerLength ->
  littleEndian lengthBytes = payloadLength ->
  littleEndian consumedBytes =
    (headerLength + payloadLength) mod word64Modulus ->
  encodeResult inputPointer input before
    (decodeItemOkBytes before pointerBytes lengthBytes consumedBytes isList)
    (candidateSuccess isList headerLength payloadLength).
Proof.
  intros Hbefore Hp Hl Hc Hpv Hlv Hcv.
  apply encodeResult_success_from_padding.
  - apply (decodeItemOkBytes_success before pointerBytes lengthBytes
      consumedBytes); assumption.
  - apply (preservedImage_of_slice before _ 17 7); try lia.
    apply decodeItemOkBytes_pad17_field; assumption.
  - apply (preservedImage_of_slice before _ 34 6); try lia.
    apply decodeItemOkBytes_pad34_field; assumption.
Qed.

Lemma errorEncoding_valueImage :
  valueImage errorEncoding 0 40
    (fun i => if Nat.eqb i 32 then 4 else 0).
Proof.
  intros i Hi.
  unfold byteAt, errorEncoding.
  replace (0 + i)%nat with i by lia.
  destruct (Nat.lt_trichotomy i 32) as [Hsmall|[Heq|Hlarge]].
  - rewrite nth_error_app1 by (rewrite repeat_length; lia).
    rewrite nth_error_repeat by lia.
    replace (Nat.eqb i 32) with false by (symmetry; apply Nat.eqb_neq; lia).
    reflexivity.
  - subst i.
    rewrite nth_error_app2 by (rewrite repeat_length; lia).
    rewrite repeat_length. simpl.
    reflexivity.
  - rewrite nth_error_app2 by (rewrite repeat_length; lia).
    rewrite repeat_length.
    rewrite nth_error_app2 by (simpl; lia).
    change (length [Values.mword_of_int 4]) with 1%nat.
    rewrite nth_error_repeat by lia.
    replace (Nat.eqb i 32) with false by (symmetry; apply Nat.eqb_neq; lia).
    reflexivity.
Qed.

Lemma errorReturnImage :
  errorResult40 errorEncoding /\
  forall inputPointer input before,
    encodeResult inputPointer input before errorEncoding candidateError.
Proof.
  split.
  - apply errorResult40_from_pointwise.
    + apply errorEncoding_length.
    + apply errorEncoding_valueImage.
  - intros.
    apply encodeResult_error_from_pointwise.
    + apply errorEncoding_length.
    + change (fieldImage (([] : list byte) ++ errorEncoding ++ [])
        (length ([] : list byte)) errorEncoding).
      apply fieldImage_middle.
Qed.

Lemma decodeItemOkBytes_otherPrefix inputPointer prefix rest before
    pointerBytes lengthBytes consumedBytes isList headerLength payloadLength :
  bv_unsigned prefix <> 128 ->
  (length before = 40)%nat ->
  (length pointerBytes = 8)%nat ->
  (length lengthBytes = 8)%nat ->
  (length consumedBytes = 8)%nat ->
  littleEndian pointerBytes = inputPointer + headerLength ->
  littleEndian lengthBytes = payloadLength ->
  littleEndian consumedBytes =
    (headerLength + payloadLength) mod word64Modulus ->
  encodeResult inputPointer (prefix :: rest) before
    (decodeItemOkBytes before pointerBytes lengthBytes consumedBytes isList)
    (candidateSuccess isList headerLength payloadLength).
Proof.
  intros Hprefix Hbefore Hp Hl Hc Hpv Hlv Hcv.
  apply decodeItemOkBytes_encodeSuccess; try assumption.
  unfold itemPayloadPointer. simpl.
  apply Z.eqb_neq in Hprefix. rewrite Hprefix.
  exact Hpv.
Qed.

(* Return 0x800d69a0 has literal and short-string incoming edges. *)
Lemma return_800d69a0_literal inputPointer prefix rest before
    pointerBytes lengthBytes consumedBytes :
  bv_unsigned prefix <= 127 ->
  (length before = 40)%nat ->
  (length pointerBytes = 8)%nat ->
  (length lengthBytes = 8)%nat ->
  (length consumedBytes = 8)%nat ->
  littleEndian pointerBytes = inputPointer ->
  littleEndian lengthBytes = 1 ->
  littleEndian consumedBytes = 1 mod word64Modulus ->
  encodeResult inputPointer (prefix :: rest) before
    (decodeItemOkBytes before pointerBytes lengthBytes consumedBytes false)
    (candidateSuccess false 0 1).
Proof.
  intros Hprefix Hbefore Hp Hl Hc Hpv Hlv Hcv.
  apply decodeItemOkBytes_otherPrefix; try assumption; lia.
Qed.

Lemma return_800d69a0_shortString inputPointer prefix rest before
    pointerBytes lengthBytes consumedBytes :
  129 <= bv_unsigned prefix <= 183 ->
  (length before = 40)%nat ->
  (length pointerBytes = 8)%nat ->
  (length lengthBytes = 8)%nat ->
  (length consumedBytes = 8)%nat ->
  littleEndian pointerBytes = inputPointer + 1 ->
  littleEndian lengthBytes = bv_unsigned prefix - 128 ->
  littleEndian consumedBytes =
    (1 + (bv_unsigned prefix - 128)) mod word64Modulus ->
  encodeResult inputPointer (prefix :: rest) before
    (decodeItemOkBytes before pointerBytes lengthBytes consumedBytes false)
    (candidateSuccess false 1 (bv_unsigned prefix - 128)).
Proof.
  intros Hprefix Hbefore Hp Hl Hc Hpv Hlv Hcv.
  apply decodeItemOkBytes_otherPrefix; try assumption; lia.
Qed.

(* Return 0x800d69d4 uses the selected empty-string pointer sentinel. *)
Lemma return_800d69d4_emptyString inputPointer prefix rest before
    pointerBytes lengthBytes consumedBytes :
  bv_unsigned prefix = 128 ->
  (length before = 40)%nat ->
  (length pointerBytes = 8)%nat ->
  (length lengthBytes = 8)%nat ->
  (length consumedBytes = 8)%nat ->
  littleEndian pointerBytes = 1 ->
  littleEndian lengthBytes = 0 ->
  littleEndian consumedBytes = 1 mod word64Modulus ->
  encodeResult inputPointer (prefix :: rest) before
    (decodeItemOkBytes before pointerBytes lengthBytes consumedBytes false)
    (candidateSuccess false 1 0).
Proof.
  intros Hprefix Hbefore Hp Hl Hc Hpv Hlv Hcv.
  apply decodeItemOkBytes_encodeSuccess; try assumption.
  unfold itemPayloadPointer. simpl. rewrite Hprefix, Hpv. reflexivity.
Qed.

(* The long-string and long-list sites retain modular consumed length. *)
Lemma return_800d6a60_longString inputPointer prefix rest before
    pointerBytes lengthBytes consumedBytes :
  184 <= bv_unsigned prefix <= 191 ->
  (length before = 40)%nat ->
  (length pointerBytes = 8)%nat ->
  (length lengthBytes = 8)%nat ->
  (length consumedBytes = 8)%nat ->
  littleEndian pointerBytes = inputPointer + 1 + (bv_unsigned prefix - 183) ->
  littleEndian lengthBytes =
    bigEndian (firstn (Z.to_nat (bv_unsigned prefix - 183)) rest) ->
  littleEndian consumedBytes =
    (1 + (bv_unsigned prefix - 183) +
     bigEndian (firstn (Z.to_nat (bv_unsigned prefix - 183)) rest))
      mod word64Modulus ->
  encodeResult inputPointer (prefix :: rest) before
    (decodeItemOkBytes before pointerBytes lengthBytes consumedBytes false)
    (candidateSuccess false (1 + (bv_unsigned prefix - 183))
      (bigEndian (firstn (Z.to_nat (bv_unsigned prefix - 183)) rest))).
Proof.
  intros Hprefix Hbefore Hp Hl Hc Hpv Hlv Hcv.
  apply decodeItemOkBytes_otherPrefix; try assumption; lia.
Qed.

Lemma return_800d6aa4_shortList inputPointer prefix rest before
    pointerBytes lengthBytes consumedBytes :
  192 <= bv_unsigned prefix <= 247 ->
  (length before = 40)%nat ->
  (length pointerBytes = 8)%nat ->
  (length lengthBytes = 8)%nat ->
  (length consumedBytes = 8)%nat ->
  littleEndian pointerBytes = inputPointer + 1 ->
  littleEndian lengthBytes = bv_unsigned prefix - 192 ->
  littleEndian consumedBytes =
    (1 + (bv_unsigned prefix - 192)) mod word64Modulus ->
  encodeResult inputPointer (prefix :: rest) before
    (decodeItemOkBytes before pointerBytes lengthBytes consumedBytes true)
    (candidateSuccess true 1 (bv_unsigned prefix - 192)).
Proof.
  intros Hprefix Hbefore Hp Hl Hc Hpv Hlv Hcv.
  apply decodeItemOkBytes_otherPrefix; try assumption; lia.
Qed.

Lemma return_800d6b04_error inputPointer input before :
  errorResult40 errorEncoding /\
  encodeResult inputPointer input before errorEncoding candidateError.
Proof.
  destruct errorReturnImage as [Himage Hencode].
  split; [exact Himage|apply Hencode].
Qed.

Lemma return_800d6b2c_longList inputPointer prefix rest before
    pointerBytes lengthBytes consumedBytes :
  248 <= bv_unsigned prefix <= 255 ->
  (length before = 40)%nat ->
  (length pointerBytes = 8)%nat ->
  (length lengthBytes = 8)%nat ->
  (length consumedBytes = 8)%nat ->
  littleEndian pointerBytes = inputPointer + 1 + (bv_unsigned prefix - 247) ->
  littleEndian lengthBytes =
    bigEndian (firstn (Z.to_nat (bv_unsigned prefix - 247)) rest) ->
  littleEndian consumedBytes =
    (1 + (bv_unsigned prefix - 247) +
     bigEndian (firstn (Z.to_nat (bv_unsigned prefix - 247)) rest))
      mod word64Modulus ->
  encodeResult inputPointer (prefix :: rest) before
    (decodeItemOkBytes before pointerBytes lengthBytes consumedBytes true)
    (candidateSuccess true (1 + (bv_unsigned prefix - 247))
      (bigEndian (firstn (Z.to_nat (bv_unsigned prefix - 247)) rest))).
Proof.
  intros Hprefix Hbefore Hp Hl Hc Hpv Hlv Hcv.
  apply decodeItemOkBytes_otherPrefix; try assumption; lia.
Qed.
