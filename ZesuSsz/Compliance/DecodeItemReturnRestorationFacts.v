Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.PureFacts.
Require Import isla.opsem.
Require Import ZesuSsz.Automation.Approved.
Require Import ZesuSsz.Contracts.RlpDecodeItem.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Require Import ZesuSsz.Contracts.DecodeItemBranchEntries.
Require Import ZesuSsz.Contracts.DecodeItemFrameImage.
From Coq Require Import List ZArith Lia.
From stdpp Require Import bitvector.definitions list_numbers.
Open Scope Z_scope.

Lemma decodeItemByteDecoderBridge (bytes : list byte) :
  RlpDecodeItem.littleEndian bytes = little_endian_to_bv 8%N bytes.
Proof.
  pose proof (little_endian_to_bv_bound 8%N bytes) as Hbounds.
  rewrite <- (bv_to_little_endian_to_bv (Z.of_nat (length bytes)) 8%N bytes eq_refl) at 1.
  apply littleEndian_machine_bytes.
  replace (8 * Z.of_nat (length bytes)) with (Z.of_nat (length bytes) * Z.of_N 8%N) by (cbn; lia).
  exact Hbounds.
Qed.

Lemma decodeItemSavedReturnDecoder (args : DecodeItemArgs) (frameBytes : list byte) :
  decodeItemSavedFrameFacts args frameBytes ->
  Z_to_bv 64%N (little_endian_to_bv 8%N (take (N.to_nat 8%N) (drop
    (Z.to_nat (decodeItemStackPointer args - RlpDecodeItem.decodeItemStackBytes + 8 -
       (decodeItemStackPointer args - RlpDecodeItem.decodeItemStackBytes))) frameBytes))) =
  Z_to_bv 64%N (decodeItemReturnAddress args).
Proof.
  intros (_ & _ & Hreturn).
  unfold word64At in Hreturn. destruct Hreturn as [_ Hreturn].
  replace (decodeItemStackPointer args - RlpDecodeItem.decodeItemStackBytes + 8 -
    (decodeItemStackPointer args - RlpDecodeItem.decodeItemStackBytes)) with 8 by lia.
  change (Z_to_bv 64%N (little_endian_to_bv 8%N (take 8%nat (drop 8%nat frameBytes))) = Z_to_bv 64%N (decodeItemReturnAddress args)).
  f_equal. rewrite <- decodeItemByteDecoderBridge. exact Hreturn.
Qed.

Lemma decodeItemStackEpilogueRestored (args : DecodeItemArgs) :
  bv_add (Z_to_bv 64%N (decodeItemStackPointer args - RlpDecodeItem.decodeItemStackBytes))
    (16%bv : bv 64%N) = Z_to_bv 64%N (decodeItemStackPointer args).
Proof. unfold RlpDecodeItem.decodeItemStackBytes. bv_solve. Qed.

Lemma decodeItemSavedFramePointerDecoder (args : DecodeItemArgs) (frameBytes : list byte) :
  decodeItemSavedFrameFacts args frameBytes ->
  Z_to_bv 64%N (little_endian_to_bv 8%N (take (N.to_nat 8%N) (drop
    (Z.to_nat (decodeItemStackPointer args - RlpDecodeItem.decodeItemStackBytes + 0 -
       (decodeItemStackPointer args - RlpDecodeItem.decodeItemStackBytes))) frameBytes))) =
  decodeItemSavedFramePointer args.
Proof.
  intros (_ & Hsaved & _).
  unfold word64At in Hsaved. destruct Hsaved as [_ Hsaved].
  replace (decodeItemStackPointer args - RlpDecodeItem.decodeItemStackBytes + 0 -
    (decodeItemStackPointer args - RlpDecodeItem.decodeItemStackBytes)) with 0 by lia.
  change (Z_to_bv 64%N (little_endian_to_bv 8%N (take 8%nat (drop 0%nat frameBytes))) = decodeItemSavedFramePointer args).
  rewrite <- decodeItemByteDecoderBridge, Hsaved.
  apply Z_to_bv_bv_unsigned.
Qed.


(* Folded facts let the existing consumer expose each equality. *)
Definition decodeItemFrameAndStackRestoration
    (args : DecodeItemArgs) (frameBytes : list byte) : Prop :=
  (Z_to_bv 64%N (little_endian_to_bv 8%N (take (N.to_nat 8%N) (drop
    (Z.to_nat (decodeItemStackPointer args - RlpDecodeItem.decodeItemStackBytes + 0 -
       (decodeItemStackPointer args - RlpDecodeItem.decodeItemStackBytes))) frameBytes))) =
  decodeItemSavedFramePointer args) /\
  (bv_add (Z_to_bv 64%N (decodeItemStackPointer args - RlpDecodeItem.decodeItemStackBytes))
    (16%bv : bv 64%N) = Z_to_bv 64%N (decodeItemStackPointer args)).

Definition decodeItemReturnRestoration
    (args : DecodeItemArgs) (frameBytes : list byte) : Prop :=
  (Z_to_bv 64%N (little_endian_to_bv 8%N (take (N.to_nat 8%N) (drop
    (Z.to_nat (decodeItemStackPointer args - RlpDecodeItem.decodeItemStackBytes + 8 -
       (decodeItemStackPointer args - RlpDecodeItem.decodeItemStackBytes))) frameBytes))) =
  Z_to_bv 64%N (decodeItemReturnAddress args)) /\ decodeItemFrameAndStackRestoration args frameBytes.

Lemma decodeItemReturnRestorationFacts
    (args : DecodeItemArgs) (frameBytes : list byte) :
  decodeItemSavedFrameFacts args frameBytes ->
  decodeItemReturnRestoration args frameBytes.
Proof.
  intros Hframe.
  unfold decodeItemReturnRestoration, decodeItemFrameAndStackRestoration.
  split.
  - exact (decodeItemSavedReturnDecoder args frameBytes Hframe).
  - split.
    + exact (decodeItemSavedFramePointerDecoder args frameBytes Hframe).
    + exact (decodeItemStackEpilogueRestored args).
Qed.

Global Instance decodeItemReturnRestorationDerivedFacts
    (args : DecodeItemArgs) (frameBytes : list byte) :
  ZesuDerivedFacts (decodeItemSavedFrameFacts args frameBytes)
    (decodeItemReturnRestoration args frameBytes).
Proof. exact (decodeItemReturnRestorationFacts args frameBytes). Qed.

Print Assumptions decodeItemByteDecoderBridge.
Print Assumptions decodeItemSavedReturnDecoder.
Print Assumptions decodeItemStackEpilogueRestored.
Print Assumptions decodeItemSavedFramePointerDecoder.
Print Assumptions decodeItemReturnRestorationFacts.
Print Assumptions decodeItemReturnRestorationDerivedFacts.
