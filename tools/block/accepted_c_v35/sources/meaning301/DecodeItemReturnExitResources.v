Require Import ZesuSsz.Automation.All.
From Coq Require Import ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.DecodeItemReturnFacts.
Require Import ZesuSsz.Contracts.RlpDecodeItem.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Require Import ZesuSsz.Contracts.RlpDecodeItemSchema.
Require Import ZesuSsz.Compliance.DecodeItemPathAgreement.
Open Scope Z_scope.

(* These compositions use the S1 semantic facts and the exact output image.
   They supply no instruction execution assumption. *)
Lemma decodeItemLiteralPostMeaning args after :
  decodeItemC1BDomain args ->
  decodeItemAcceptedFacts args false 0 1 ->
  encodeResult (decodeItemInputPointer args) (decodeItemInputBytes args)
    (decodeItemBeforeStorage args) after (candidateSuccess false 0 1) ->
  DecodeMeaningModuloKnownBugs args after.
Proof.
  intros Hdomain [Hcandidate Hsail] Himage.
  eapply decodeItemLiteralReturn; eauto.
Qed.

Lemma decodeItemEmptyStringPostMeaning args after :
  decodeItemC1BDomain args ->
  decodeItemAcceptedFacts args false 1 0 ->
  encodeResult (decodeItemInputPointer args) (decodeItemInputBytes args)
    (decodeItemBeforeStorage args) after (candidateSuccess false 1 0) ->
  DecodeMeaningModuloKnownBugs args after.
Proof.
  intros Hdomain [Hcandidate Hsail] Himage.
  eapply decodeItemEmptyStringReturn; eauto.
Qed.

Lemma decodeItemClassShortPostMeaning args after payloadLength (isList : bool) :
  decodeItemC1BDomain args ->
  decodeItemAcceptedFacts args isList 1 payloadLength ->
  encodeResult (decodeItemInputPointer args) (decodeItemInputBytes args)
    (decodeItemBeforeStorage args) after
    (candidateSuccess isList 1 payloadLength) ->
  0 <= payloadLength -> 1 + payloadLength < word64Modulus ->
  DecodeMeaningModuloKnownBugs args after.
Proof.
  intros Hdomain [Hcandidate Hsail] Himage Hnonnegative Hbound.
  eapply decodeItemClassShortReturn; eauto.
Qed.

Definition decodeItemShortStringPostMeaning args after payloadLength :=
  decodeItemClassShortPostMeaning args after payloadLength false.

Definition decodeItemShortListPostMeaning args after payloadLength :=
  decodeItemClassShortPostMeaning args after payloadLength true.

Lemma decodeItemClassLongPostMeaning args after headerLength payloadLength (isList : bool) :
  decodeItemC1BDomain args ->
  decodeItemLongAcceptedFacts args isList headerLength payloadLength ->
  encodeResult (decodeItemInputPointer args) (decodeItemInputBytes args)
    (decodeItemBeforeStorage args) after
    (candidateSuccess isList headerLength payloadLength) ->
  2 <= headerLength <= 9 -> 0 <= payloadLength ->
  DecodeMeaningModuloKnownBugs args after.
Proof.
  intros Hdomain [Hcandidate Hpath] Himage Hwidth Hnonnegative.
  eapply decodeItemClassLongReturn; eauto.
Qed.

Definition decodeItemLongStringPostMeaning args after headerLength payloadLength :=
  decodeItemClassLongPostMeaning args after headerLength payloadLength false.

Definition decodeItemLongListPostMeaning args after headerLength payloadLength :=
  decodeItemClassLongPostMeaning args after headerLength payloadLength true.

Lemma decodeItemErrorPostMeaning args after :
  decodeItemC1BDomain args ->
  decodeItemRejectedFacts args ->
  errorResult40 after ->
  encodeResult (decodeItemInputPointer args) (decodeItemInputBytes args)
    (decodeItemBeforeStorage args) after candidateError ->
  DecodeMeaningModuloKnownBugs args after.
Proof.
  intros Hdomain [Hcandidate Hreject] Herror Himage.
  eapply decodeItemErrorReturn; eauto.
Qed.
