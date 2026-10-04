Require Import ZesuSsz.Automation.All.
From Coq Require Import Lia List ZArith.
From stdpp Require Import bitvector.definitions.
Require Import SailStdpp.MachineWord.
Require Import EvmSailRlp.evm_rlp_types.
Require Import ZesuSsz.Compliance.SailRun.
Require Import ZesuSsz.Compliance.KnownBugs.
Require Import ZesuSsz.Contracts.RlpDecodeItem.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Require Import ZesuSsz.Contracts.RlpDecodeItemSchema.
Import ListNotations.
Open Scope Z_scope.

(* Each success observation names the fixed SailRun evaluator on the same
   bytes as the machine result. The field metadata must match the return. *)
Definition decodeItemSailSuccess (args : DecodeItemArgs)
    (isList : bool) (headerLength payloadLength : Z) : Prop :=
  exists fullLength contentLength
      (field : RlpFieldRef 0 fullLength contentLength),
    runRlpDecodeItem (decodeItemInputBytes args) (decodeItemSailCursor args) =
      Success (@existT Z (fun full => {content : Z & RlpFieldRef 0 full content})
        fullLength
        (@existT Z (fun content => RlpFieldRef 0 fullLength content)
          contentLength field)) /\
    RlpFieldRef_is_list field = isList /\
    fullLength - contentLength = headerLength /\
    contentLength = payloadLength.

Lemma decodeItemDomainInputFits args :
  decodeItemC1BDomain args ->
  inputAddressFits (decodeItemInputPointer args) (decodeItemInputBytes args).
Proof.
  intros [Hlength [_ Hlayout]].
  unfold decodeItemEntryLayout in Hlayout.
  destruct Hlayout as [Hnonnegative [_ [Hend _]]].
  unfold inputAddressFits. rewrite <- Hlength. auto.
Qed.

Lemma decodeItemSuccessAgreement args after isList headerLength payloadLength :
  decodeItemC1BDomain args ->
  candidateDecodeItem (decodeItemInputBytes args) =
    candidateSuccess isList headerLength payloadLength ->
  encodeResult (decodeItemInputPointer args) (decodeItemInputBytes args)
    (decodeItemBeforeStorage args) after
    (candidateSuccess isList headerLength payloadLength) ->
  0 <= headerLength -> 0 <= payloadLength ->
  headerLength + payloadLength < word64Modulus ->
  decodeItemSailSuccess args isList headerLength payloadLength ->
  DecodeMeaningModuloKnownBugs args after.
Proof.
  intros Hdomain Hcandidate Himage Hheader Hpayload Hfits Hsail.
  unfold DecodeMeaningModuloKnownBugs. split.
  - unfold decodeItemAllowsC1B, decodeItemAllows, C1BResult.
    split; [now apply decodeItemDomainInputFits|].
    split.
    + unfold candidateResult40. rewrite Hcandidate.
      unfold encodeResult in Himage.
      destruct Himage as [pad17 [pad34 [_ [_ [_ [_ [_ [_ Hresult]]]]]]]].
      exact Hresult.
    + rewrite Hcandidate. left. unfold noWrapConsumed.
      repeat split; try lia; apply Z.mod_small; lia.
  - left. unfold decodeItemSailResult.
    destruct Hsail as [fullLength [contentLength [field
      [Hrun [Hlist [Hlength Hcontent]]]]]].
    rewrite Hrun. unfold relateItem. simpl.
    rewrite Hlist, Hlength, Hcontent. exact Himage.
Qed.

Lemma decodeItemWrapAgreement args after isList headerLength payloadLength :
  decodeItemC1BDomain args ->
  candidateDecodeItem (decodeItemInputBytes args) =
    candidateSuccess isList headerLength payloadLength ->
  encodeResult (decodeItemInputPointer args) (decodeItemInputBytes args)
    (decodeItemBeforeStorage args) after
    (candidateSuccess isList headerLength payloadLength) ->
  binaryWrapCase headerLength payloadLength
    ((headerLength + payloadLength) mod word64Modulus) ->
  runRlpDecodeItem (decodeItemInputBytes args) (decodeItemSailCursor args) =
    Reject RlpDecode ->
  DecodeMeaningModuloKnownBugs args after.
Proof.
  intros Hdomain Hcandidate Himage Hwrap Hreject.
  unfold DecodeMeaningModuloKnownBugs. split.
  - unfold decodeItemAllowsC1B, decodeItemAllows, C1BResult.
    split; [now apply decodeItemDomainInputFits|].
    split.
    + unfold candidateResult40. rewrite Hcandidate.
      unfold encodeResult in Himage.
      destruct Himage as [pad17 [pad34 [_ [_ [_ [_ [_ [_ Hresult]]]]]]]].
      exact Hresult.
    + rewrite Hcandidate. right. exact Hwrap.
  - right. exists RlpLongLengthWrap. split; [simpl; auto|].
    unfold decodeItemBugApplies. exists isList, headerLength, payloadLength.
    split; [exact Hcandidate|]. split; [exact Hwrap|].
    split; [|exact Hreject].
    unfold candidateResult40. rewrite Hcandidate.
    unfold encodeResult in Himage.
    destruct Himage as [pad17 [pad34 [_ [_ [_ [_ [_ [_ Hresult]]]]]]]].
    exact Hresult.
Qed.

Lemma decodeItemRejectAgreement args after :
  decodeItemC1BDomain args ->
  candidateDecodeItem (decodeItemInputBytes args) = candidateError ->
  errorResult40 after ->
  encodeResult (decodeItemInputPointer args) (decodeItemInputBytes args)
    (decodeItemBeforeStorage args) after candidateError ->
  runRlpDecodeItem (decodeItemInputBytes args) (decodeItemSailCursor args) =
    Reject RlpDecode ->
  DecodeMeaningModuloKnownBugs args after.
Proof.
  intros Hdomain Hcandidate Hresult Himage Hreject.
  unfold DecodeMeaningModuloKnownBugs. split.
  - unfold decodeItemAllowsC1B, decodeItemAllows, C1BResult.
    split; [now apply decodeItemDomainInputFits|].
    split; [unfold candidateResult40; now rewrite Hcandidate|].
    now rewrite Hcandidate.
  - left. unfold decodeItemSailResult. rewrite Hreject.
    unfold relateItem. exact Himage.
Qed.

(* 0x800d69a0 has two incoming success classes. *)
Lemma decodeItemLiteralReturn args after :
  decodeItemC1BDomain args ->
  candidateDecodeItem (decodeItemInputBytes args) = candidateSuccess false 0 1 ->
  encodeResult (decodeItemInputPointer args) (decodeItemInputBytes args)
    (decodeItemBeforeStorage args) after (candidateSuccess false 0 1) ->
  decodeItemSailSuccess args false 0 1 ->
  DecodeMeaningModuloKnownBugs args after.
Proof. intros. eapply decodeItemSuccessAgreement; eauto; unfold word64Modulus; lia. Qed.

Lemma decodeItemShortStringReturn args after payloadLength :
  decodeItemC1BDomain args ->
  candidateDecodeItem (decodeItemInputBytes args) =
    candidateSuccess false 1 payloadLength ->
  encodeResult (decodeItemInputPointer args) (decodeItemInputBytes args)
    (decodeItemBeforeStorage args) after
    (candidateSuccess false 1 payloadLength) ->
  0 <= payloadLength -> 1 + payloadLength < word64Modulus ->
  decodeItemSailSuccess args false 1 payloadLength ->
  DecodeMeaningModuloKnownBugs args after.
Proof. intros. eapply decodeItemSuccessAgreement; eauto; unfold word64Modulus; lia. Qed.

(* 0x800d69d4 returns the empty-string sentinel pointer. *)
Lemma decodeItemEmptyStringReturn args after :
  decodeItemC1BDomain args ->
  candidateDecodeItem (decodeItemInputBytes args) = candidateSuccess false 1 0 ->
  encodeResult (decodeItemInputPointer args) (decodeItemInputBytes args)
    (decodeItemBeforeStorage args) after (candidateSuccess false 1 0) ->
  decodeItemSailSuccess args false 1 0 ->
  DecodeMeaningModuloKnownBugs args after.
Proof. intros. eapply decodeItemSuccessAgreement; eauto; unfold word64Modulus; lia. Qed.

(* 0x800d6aa4 is the short-list return. *)
Lemma decodeItemShortListReturn args after payloadLength :
  decodeItemC1BDomain args ->
  candidateDecodeItem (decodeItemInputBytes args) =
    candidateSuccess true 1 payloadLength ->
  encodeResult (decodeItemInputPointer args) (decodeItemInputBytes args)
    (decodeItemBeforeStorage args) after
    (candidateSuccess true 1 payloadLength) ->
  0 <= payloadLength -> 1 + payloadLength < word64Modulus ->
  decodeItemSailSuccess args true 1 payloadLength ->
  DecodeMeaningModuloKnownBugs args after.
Proof. intros. eapply decodeItemSuccessAgreement; eauto; unfold word64Modulus; lia. Qed.

(* 0x800d6a60 and 0x800d6b2c each allow the selected wrap bug. *)
Lemma decodeItemLongStringReturn args after headerLength payloadLength :
  decodeItemC1BDomain args ->
  candidateDecodeItem (decodeItemInputBytes args) =
    candidateSuccess false headerLength payloadLength ->
  encodeResult (decodeItemInputPointer args) (decodeItemInputBytes args)
    (decodeItemBeforeStorage args) after
    (candidateSuccess false headerLength payloadLength) ->
  (2 <= headerLength <= 9) -> 0 <= payloadLength ->
  ((headerLength + payloadLength < word64Modulus /\
    decodeItemSailSuccess args false headerLength payloadLength) \/
   (binaryWrapCase headerLength payloadLength
      ((headerLength + payloadLength) mod word64Modulus) /\
    runRlpDecodeItem (decodeItemInputBytes args) (decodeItemSailCursor args) =
      Reject RlpDecode)) ->
  DecodeMeaningModuloKnownBugs args after.
Proof.
  intros Hdomain Hcandidate Himage Hwidth Hpayload [[Hfits Hsail]|[Hwrap Hreject]].
  - eapply decodeItemSuccessAgreement; eauto; lia.
  - eapply decodeItemWrapAgreement; eauto.
Qed.

Lemma decodeItemLongListReturn args after headerLength payloadLength :
  decodeItemC1BDomain args ->
  candidateDecodeItem (decodeItemInputBytes args) =
    candidateSuccess true headerLength payloadLength ->
  encodeResult (decodeItemInputPointer args) (decodeItemInputBytes args)
    (decodeItemBeforeStorage args) after
    (candidateSuccess true headerLength payloadLength) ->
  (2 <= headerLength <= 9) -> 0 <= payloadLength ->
  ((headerLength + payloadLength < word64Modulus /\
    decodeItemSailSuccess args true headerLength payloadLength) \/
   (binaryWrapCase headerLength payloadLength
      ((headerLength + payloadLength) mod word64Modulus) /\
    runRlpDecodeItem (decodeItemInputBytes args) (decodeItemSailCursor args) =
      Reject RlpDecode)) ->
  DecodeMeaningModuloKnownBugs args after.
Proof.
  intros Hdomain Hcandidate Himage Hwidth Hpayload [[Hfits Hsail]|[Hwrap Hreject]].
  - eapply decodeItemSuccessAgreement; eauto; lia.
  - eapply decodeItemWrapAgreement; eauto.
Qed.

(* 0x800d6b04 covers every rejected header or payload check. *)
Lemma decodeItemErrorReturn args after :
  decodeItemC1BDomain args ->
  candidateDecodeItem (decodeItemInputBytes args) = candidateError ->
  errorResult40 after ->
  encodeResult (decodeItemInputPointer args) (decodeItemInputBytes args)
    (decodeItemBeforeStorage args) after candidateError ->
  runRlpDecodeItem (decodeItemInputBytes args) (decodeItemSailCursor args) =
    Reject RlpDecode ->
  DecodeMeaningModuloKnownBugs args after.
Proof. exact (decodeItemRejectAgreement args after). Qed.

(* Q23 pins these three eight-byte length wraps. The following computations
   check the concrete Sail action and candidate class, not an ELF execution. *)
Definition q23WrapStringPlusOne : list byte :=
  map (Z_to_bv 8) [191; 255; 255; 255; 255; 255; 255; 255; 248].

Definition q23WrapList : list byte :=
  map (Z_to_bv 8) [255; 255; 255; 255; 255; 255; 255; 255; 247].

Definition q23WrapCursor : RlpCursor 0 9 :=
  {| StatelessInputSliceFields_bytes := 0;
     StatelessInputSliceFields_len := 9 |}.

Lemma q23WrapCandidateClasses :
  candidateDecodeItem decodeItemWrapWitnessInput =
    candidateSuccess false 9 (word64Modulus - 9) /\
  candidateDecodeItem q23WrapStringPlusOne =
    candidateSuccess false 9 (word64Modulus - 8) /\
  candidateDecodeItem q23WrapList =
    candidateSuccess true 9 (word64Modulus - 9).
Proof. vm_compute. repeat split; reflexivity. Qed.

Lemma q23WrapSailRejects :
  runRlpDecodeItem decodeItemWrapWitnessInput q23WrapCursor = Reject RlpDecode /\
  runRlpDecodeItem q23WrapStringPlusOne q23WrapCursor = Reject RlpDecode /\
  runRlpDecodeItem q23WrapList q23WrapCursor = Reject RlpDecode.
Proof. vm_compute. repeat split; reflexivity. Qed.

Lemma q23LongStringWrapMeaning args after :
  decodeItemC1BDomain args ->
  decodeItemInputBytes args = decodeItemWrapWitnessInput ->
  encodeResult (decodeItemInputPointer args) (decodeItemInputBytes args)
    (decodeItemBeforeStorage args) after
    (candidateSuccess false 9 (word64Modulus - 9)) ->
  DecodeMeaningModuloKnownBugs args after.
Proof.
  intros Hdomain Hbytes Himage.
  eapply decodeItemWrapAgreement; [exact Hdomain| |exact Himage| |].
  - rewrite Hbytes. exact (proj1 q23WrapCandidateClasses).
  - exact (proj1 (proj2 decodeItemWrapWitness)).
  - unfold decodeItemSailCursor. rewrite Hbytes.
    exact (proj1 q23WrapSailRejects).
Qed.

Print Assumptions decodeItemLiteralReturn.
Print Assumptions decodeItemShortStringReturn.
Print Assumptions decodeItemEmptyStringReturn.
Print Assumptions decodeItemLongStringReturn.
Print Assumptions decodeItemShortListReturn.
Print Assumptions decodeItemLongListReturn.
Print Assumptions decodeItemErrorReturn.
Print Assumptions q23WrapCandidateClasses.
Print Assumptions q23WrapSailRejects.
Print Assumptions q23LongStringWrapMeaning.
