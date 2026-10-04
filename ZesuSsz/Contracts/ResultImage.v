From Coq Require Import List Lia ZArith.
Require Import SailStdpp.MachineWord EvmSailRlp.evm_rlp_types.
Require Import ZesuSsz.Contracts.RlpDecodeItem.
Require Import ZesuSsz.Contracts.RlpDecodeItemSchema.
Import ListNotations.
Open Scope Z_scope.

Definition fieldImage (bytes : list byte) (offset : nat)
    (field : list byte) : Prop :=
  forall i, (i < length field)%nat ->
    nth_error bytes (offset + i) = nth_error field i.

Definition valueImage (bytes : list byte) (offset count : nat)
    (value : nat -> Z) : Prop :=
  forall i, (i < count)%nat -> byteAt bytes (offset + i) (value i).

Definition preservedImage (before after : list byte) (offset count : nat) : Prop :=
  forall i, (i < count)%nat ->
    nth_error after (offset + i) = nth_error before (offset + i).

Lemma nth_error_skipn_offset {A : Type} (xs : list A) offset i :
    nth_error (skipn offset xs) i = nth_error xs (offset + i).
Proof.
  revert xs i.
  induction offset as [|offset IH]; intros [|x xs] i; simpl; auto.
  destruct i; reflexivity.
Qed.

Lemma nth_error_firstn_inside {A : Type} (xs : list A) count i :
    (i < count)%nat ->
    nth_error (firstn count xs) i = nth_error xs i.
Proof.
  revert xs i.
  induction count as [|count IH]; intros xs i Hi; [lia|].
  destruct xs as [|x xs]; [destruct i; reflexivity|].
  destruct i as [|i]; simpl; [reflexivity|].
  apply IH. lia.
Qed.

Lemma fieldImage_slice (bytes field : list byte) offset :
    fieldImage bytes offset field ->
    firstn (length field) (skipn offset bytes) = field.
Proof.
  intros Himage.
  apply nth_error_ext; intro i.
  destruct (Nat.lt_ge_cases i (length field)) as [Hi|Hi].
  - rewrite nth_error_firstn_inside by exact Hi.
    rewrite nth_error_skipn_offset.
    apply Himage. exact Hi.
  - rewrite (proj2 (nth_error_None _ i)).
    2: { rewrite firstn_length. lia. }
    rewrite (proj2 (nth_error_None _ i)) by exact Hi.
    reflexivity.
Qed.

Lemma word64At_from_field (bytes field : list byte) offset value :
    (length field = 8)%nat ->
    fieldImage bytes offset field ->
    littleEndian field = value ->
    word64At bytes offset value.
Proof.
  intros Hlength Himage Hvalue.
  unfold word64At.
  rewrite <- Hlength.
  rewrite (fieldImage_slice bytes field offset Himage).
  auto.
Qed.

Lemma successResult40_from_images
    (before after pointerBytes lengthBytes consumedBytes : list byte)
    (payloadPointer payloadLength consumed : Z) (isList : bool) :
    (length before = 40)%nat ->
    (length after = 40)%nat ->
    (length pointerBytes = 8)%nat ->
    (length lengthBytes = 8)%nat ->
    (length consumedBytes = 8)%nat ->
    fieldImage after 0 pointerBytes ->
    fieldImage after 8 lengthBytes ->
    fieldImage after 24 consumedBytes ->
    littleEndian pointerBytes = payloadPointer ->
    littleEndian lengthBytes = payloadLength ->
    littleEndian consumedBytes = consumed ->
    byteAt after 16 (if isList then 1 else 0) ->
    byteAt after 32 0 ->
    byteAt after 33 0 ->
    preservedImage before after 17 7 ->
    preservedImage before after 34 6 ->
    successResult40 before after payloadPointer payloadLength isList consumed.
Proof.
  intros Hbefore Hafter HpLen HlLen HcLen Hp Hl Hc
    HpValue HlValue HcValue Hflag Hstatus0 Hstatus1 Hpad1 Hpad2.
  unfold successResult40.
  split; [exact Hbefore|].
  split; [exact Hafter|].
  split; [apply (word64At_from_field after pointerBytes 0 payloadPointer);
          assumption|].
  split; [apply (word64At_from_field after lengthBytes 8 payloadLength);
          assumption|].
  split; [exact Hflag|].
  split; [apply (word64At_from_field after consumedBytes 24 consumed);
          assumption|].
  split; [exact Hstatus0|].
  split; [exact Hstatus1|].
  intros i [[Hlo Hhi]|[Hlo Hhi]].
  - replace i with (17 + (i - 17))%nat by lia.
    apply Hpad1. lia.
  - replace i with (34 + (i - 34))%nat by lia.
    apply Hpad2. lia.
Qed.

Lemma errorResult40_from_pointwise (after : list byte) :
    (length after = 40)%nat ->
    valueImage after 0 40 (fun i => if Nat.eqb i 32 then 4 else 0) ->
    errorResult40 after.
Proof.
  intros Hlength Himage.
  unfold errorResult40.
  split; [exact Hlength|].
  intros i Hi.
  apply Himage. exact Hi.
Qed.

Lemma fieldImage_entire (bytes field : list byte) :
    length bytes = length field ->
    fieldImage bytes 0 field ->
    bytes = field.
Proof.
  intros Hlength Himage.
  apply nth_error_ext; intro i.
  destruct (Nat.lt_ge_cases i (length field)) as [Hi|Hi].
  - apply Himage. exact Hi.
  - rewrite (proj2 (nth_error_None _ i)) by lia.
    rewrite (proj2 (nth_error_None _ i)) by exact Hi.
    reflexivity.
Qed.

Lemma preservedImage_slice (before after : list byte) offset count :
    preservedImage before after offset count ->
    firstn count (skipn offset after) =
      firstn count (skipn offset before).
Proof.
  intros Hpreserve.
  apply nth_error_ext; intro i.
  destruct (Nat.lt_ge_cases i count) as [Hi|Hi].
  - repeat rewrite nth_error_firstn_inside by exact Hi.
    repeat rewrite nth_error_skipn_offset.
    apply Hpreserve. exact Hi.
  - rewrite (proj2 (nth_error_None _ i)).
    2: { rewrite firstn_length. lia. }
    rewrite (proj2 (nth_error_None _ i)).
    2: { rewrite firstn_length. lia. }
    reflexivity.
Qed.

Lemma errorEncoding_length : (length errorEncoding = 40)%nat.
Proof.
  unfold errorEncoding.
  repeat rewrite app_length.
  repeat rewrite repeat_length.
  simpl. lia.
Qed.

Lemma encodeResult_error_from_pointwise
    (inputPointer : Z) (input before after : list byte) :
    (length after = 40)%nat ->
    fieldImage after 0 errorEncoding ->
    encodeResult inputPointer input before after candidateError.
Proof.
  intros Hlength Himage.
  unfold encodeResult.
  apply fieldImage_entire; [rewrite errorEncoding_length; exact Hlength|exact Himage].
Qed.

Lemma encodeResult_success_from_padding
    (inputPointer : Z) (input before after : list byte)
    (isList : bool) (headerLength payloadLength : Z) :
    successResult40 before after
      (itemPayloadPointer inputPointer input headerLength)
      payloadLength isList
      ((headerLength + payloadLength) mod word64Modulus) ->
    preservedImage before after 17 7 ->
    preservedImage before after 34 6 ->
    encodeResult inputPointer input before after
      (candidateSuccess isList headerLength payloadLength).
Proof.
  intros Hsuccess Hpad17 Hpad34.
  pose proof Hsuccess as [Hbefore [Hafter _]].
  unfold encodeResult.
  exists (firstn 7 (skipn 17 before)), (firstn 6 (skipn 34 before)).
  split.
  - rewrite firstn_length, skipn_length, Hbefore.
    rewrite Nat.min_l; lia.
  - split.
    + rewrite firstn_length, skipn_length, Hbefore.
      rewrite Nat.min_l; lia.
    + split; [reflexivity|].
      split; [reflexivity|].
      split; [symmetry; apply preservedImage_slice; exact Hpad17|].
      split; [symmetry; apply preservedImage_slice; exact Hpad34|].
      exact Hsuccess.
Qed.

Lemma encodeResult_success_from_images
    (inputPointer : Z)
    (input before after pointerBytes lengthBytes consumedBytes : list byte)
    (isList : bool) (headerLength payloadLength : Z) :
    (length before = 40)%nat ->
    (length after = 40)%nat ->
    (length pointerBytes = 8)%nat ->
    (length lengthBytes = 8)%nat ->
    (length consumedBytes = 8)%nat ->
    fieldImage after 0 pointerBytes ->
    fieldImage after 8 lengthBytes ->
    fieldImage after 24 consumedBytes ->
    littleEndian pointerBytes =
      itemPayloadPointer inputPointer input headerLength ->
    littleEndian lengthBytes = payloadLength ->
    littleEndian consumedBytes =
      (headerLength + payloadLength) mod word64Modulus ->
    byteAt after 16 (if isList then 1 else 0) ->
    byteAt after 32 0 ->
    byteAt after 33 0 ->
    preservedImage before after 17 7 ->
    preservedImage before after 34 6 ->
    encodeResult inputPointer input before after
      (candidateSuccess isList headerLength payloadLength).
Proof.
  intros Hbefore Hafter HpLen HlLen HcLen Hp Hl Hc
    HpValue HlValue HcValue Hflag Hstatus0 Hstatus1 Hpad17 Hpad34.
  apply encodeResult_success_from_padding.
  - apply (successResult40_from_images before after pointerBytes lengthBytes
      consumedBytes (itemPayloadPointer inputPointer input headerLength)
      payloadLength ((headerLength + payloadLength) mod word64Modulus)
      isList); assumption.
  - exact Hpad17.
  - exact Hpad34.
Qed.
