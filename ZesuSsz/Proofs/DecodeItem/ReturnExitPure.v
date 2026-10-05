Require Import ZesuSsz.Automation.All.
From Coq Require Import List ZArith Lia.
From stdpp Require Import bitvector.definitions.
Require Import SailStdpp.MachineWord EvmSailRlp.evm_rlp_types.
Require Import ZesuSsz.Contracts.RlpDecodeItem.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Require Import ZesuSsz.Contracts.RlpDecodeItemSchema.
Require Import ZesuSsz.Contracts.RlpDecodeItemReturnImages.
Require Import ZesuSsz.Compliance.SailRun.
Require Import ZesuSsz.Compliance.DecodeItemPathAgreement.
Import ListNotations.
Open Scope Z_scope.

(* Each lemma connects an exact Q44 byte image to the Q45 path fact.
   Machine ownership and writes at these PCs remain block obligations. *)
Lemma returnExitLiteral args prefix rest pointerBytes lengthBytes consumedBytes :
  decodeItemInputBytes args = prefix :: rest ->
  decodeItemC1BDomain args ->
  bv_unsigned prefix <= 127 ->
  (length (decodeItemBeforeStorage args) = 40)%nat ->
  (length pointerBytes = 8)%nat ->
  (length lengthBytes = 8)%nat ->
  (length consumedBytes = 8)%nat ->
  littleEndian pointerBytes = decodeItemInputPointer args ->
  littleEndian lengthBytes = 1 ->
  littleEndian consumedBytes = 1 mod word64Modulus ->
  candidateDecodeItem (decodeItemInputBytes args) = candidateSuccess false 0 1 ->
  decodeItemSailSuccess args false 0 1 ->
  DecodeMeaningModuloKnownBugs args
    (decodeItemOkBytes (decodeItemBeforeStorage args)
       pointerBytes lengthBytes consumedBytes false).
Proof.
  intros Hinput Hdomain Hprefix Hbefore Hp Hl Hc Hpv Hlv Hcv Hcandidate Hsail.
  eapply decodeItemLiteralReturn; [exact Hdomain|exact Hcandidate| |exact Hsail].
  rewrite Hinput.
  eapply return_800d69a0_literal; eauto.
Qed.

Lemma returnExitShortString args prefix rest pointerBytes lengthBytes consumedBytes :
  decodeItemInputBytes args = prefix :: rest ->
  decodeItemC1BDomain args ->
  129 <= bv_unsigned prefix <= 183 ->
  (length (decodeItemBeforeStorage args) = 40)%nat ->
  (length pointerBytes = 8)%nat ->
  (length lengthBytes = 8)%nat ->
  (length consumedBytes = 8)%nat ->
  littleEndian pointerBytes = decodeItemInputPointer args + 1 ->
  littleEndian lengthBytes = bv_unsigned prefix - 128 ->
  littleEndian consumedBytes =
    (1 + (bv_unsigned prefix - 128)) mod word64Modulus ->
  candidateDecodeItem (decodeItemInputBytes args) =
    candidateSuccess false 1 (bv_unsigned prefix - 128) ->
  decodeItemSailSuccess args false 1 (bv_unsigned prefix - 128) ->
  DecodeMeaningModuloKnownBugs args
    (decodeItemOkBytes (decodeItemBeforeStorage args)
       pointerBytes lengthBytes consumedBytes false).
Proof.
  intros Hinput Hdomain Hprefix Hbefore Hp Hl Hc Hpv Hlv Hcv Hcandidate Hsail.
  eapply decodeItemShortStringReturn;
    [exact Hdomain|exact Hcandidate| |lia| |exact Hsail].
  - rewrite Hinput. eapply return_800d69a0_shortString; eauto.
  - unfold word64Modulus. lia.
Qed.

Lemma returnExitEmptyString args prefix rest pointerBytes lengthBytes consumedBytes :
  decodeItemInputBytes args = prefix :: rest ->
  decodeItemC1BDomain args ->
  bv_unsigned prefix = 128 ->
  (length (decodeItemBeforeStorage args) = 40)%nat ->
  (length pointerBytes = 8)%nat ->
  (length lengthBytes = 8)%nat ->
  (length consumedBytes = 8)%nat ->
  littleEndian pointerBytes = 1 ->
  littleEndian lengthBytes = 0 ->
  littleEndian consumedBytes = 1 mod word64Modulus ->
  candidateDecodeItem (decodeItemInputBytes args) = candidateSuccess false 1 0 ->
  decodeItemSailSuccess args false 1 0 ->
  DecodeMeaningModuloKnownBugs args
    (decodeItemOkBytes (decodeItemBeforeStorage args)
       pointerBytes lengthBytes consumedBytes false).
Proof.
  intros Hinput Hdomain Hprefix Hbefore Hp Hl Hc Hpv Hlv Hcv Hcandidate Hsail.
  eapply decodeItemEmptyStringReturn; [exact Hdomain|exact Hcandidate| |exact Hsail].
  rewrite Hinput. eapply return_800d69d4_emptyString; eauto.
Qed.

Lemma returnExitShortList args prefix rest pointerBytes lengthBytes consumedBytes :
  decodeItemInputBytes args = prefix :: rest ->
  decodeItemC1BDomain args ->
  192 <= bv_unsigned prefix <= 247 ->
  (length (decodeItemBeforeStorage args) = 40)%nat ->
  (length pointerBytes = 8)%nat ->
  (length lengthBytes = 8)%nat ->
  (length consumedBytes = 8)%nat ->
  littleEndian pointerBytes = decodeItemInputPointer args + 1 ->
  littleEndian lengthBytes = bv_unsigned prefix - 192 ->
  littleEndian consumedBytes =
    (1 + (bv_unsigned prefix - 192)) mod word64Modulus ->
  candidateDecodeItem (decodeItemInputBytes args) =
    candidateSuccess true 1 (bv_unsigned prefix - 192) ->
  decodeItemSailSuccess args true 1 (bv_unsigned prefix - 192) ->
  DecodeMeaningModuloKnownBugs args
    (decodeItemOkBytes (decodeItemBeforeStorage args)
       pointerBytes lengthBytes consumedBytes true).
Proof.
  intros Hinput Hdomain Hprefix Hbefore Hp Hl Hc Hpv Hlv Hcv Hcandidate Hsail.
  eapply decodeItemShortListReturn;
    [exact Hdomain|exact Hcandidate| |lia| |exact Hsail].
  - rewrite Hinput. eapply return_800d6aa4_shortList; eauto.
  - unfold word64Modulus. lia.
Qed.

Lemma returnExitLongString args prefix rest pointerBytes lengthBytes consumedBytes
    headerLength payloadLength :
  decodeItemInputBytes args = prefix :: rest ->
  decodeItemC1BDomain args ->
  184 <= bv_unsigned prefix <= 191 ->
  headerLength = 1 + (bv_unsigned prefix - 183) ->
  payloadLength = bigEndian (firstn (Z.to_nat (bv_unsigned prefix - 183)) rest) ->
  0 <= payloadLength ->
  (length (decodeItemBeforeStorage args) = 40)%nat ->
  (length pointerBytes = 8)%nat ->
  (length lengthBytes = 8)%nat ->
  (length consumedBytes = 8)%nat ->
  littleEndian pointerBytes = decodeItemInputPointer args + headerLength ->
  littleEndian lengthBytes = payloadLength ->
  littleEndian consumedBytes =
    (headerLength + payloadLength) mod word64Modulus ->
  candidateDecodeItem (decodeItemInputBytes args) =
    candidateSuccess false headerLength payloadLength ->
  ((headerLength + payloadLength < word64Modulus /\
    decodeItemSailSuccess args false headerLength payloadLength) \/
   (binaryWrapCase headerLength payloadLength
      ((headerLength + payloadLength) mod word64Modulus) /\
    runRlpDecodeItem (decodeItemInputBytes args) (decodeItemSailCursor args) =
      Reject RlpDecode)) ->
  DecodeMeaningModuloKnownBugs args
    (decodeItemOkBytes (decodeItemBeforeStorage args)
       pointerBytes lengthBytes consumedBytes false).
Proof.
  intros Hinput Hdomain Hprefix Hheader Hpayload Hnonnegative
    Hbefore Hp Hl Hc Hpv Hlv Hcv Hcandidate Hpath.
  eapply decodeItemLongStringReturn;
    [exact Hdomain|exact Hcandidate| |lia|exact Hnonnegative|exact Hpath].
  rewrite Hinput. subst headerLength payloadLength.
  eapply return_800d6a60_longString; eauto.
  rewrite Hpv. now rewrite Z.add_assoc.
Qed.

Lemma returnExitLongList args prefix rest pointerBytes lengthBytes consumedBytes
    headerLength payloadLength :
  decodeItemInputBytes args = prefix :: rest ->
  decodeItemC1BDomain args ->
  248 <= bv_unsigned prefix <= 255 ->
  headerLength = 1 + (bv_unsigned prefix - 247) ->
  payloadLength = bigEndian (firstn (Z.to_nat (bv_unsigned prefix - 247)) rest) ->
  0 <= payloadLength ->
  (length (decodeItemBeforeStorage args) = 40)%nat ->
  (length pointerBytes = 8)%nat ->
  (length lengthBytes = 8)%nat ->
  (length consumedBytes = 8)%nat ->
  littleEndian pointerBytes = decodeItemInputPointer args + headerLength ->
  littleEndian lengthBytes = payloadLength ->
  littleEndian consumedBytes =
    (headerLength + payloadLength) mod word64Modulus ->
  candidateDecodeItem (decodeItemInputBytes args) =
    candidateSuccess true headerLength payloadLength ->
  ((headerLength + payloadLength < word64Modulus /\
    decodeItemSailSuccess args true headerLength payloadLength) \/
   (binaryWrapCase headerLength payloadLength
      ((headerLength + payloadLength) mod word64Modulus) /\
    runRlpDecodeItem (decodeItemInputBytes args) (decodeItemSailCursor args) =
      Reject RlpDecode)) ->
  DecodeMeaningModuloKnownBugs args
    (decodeItemOkBytes (decodeItemBeforeStorage args)
       pointerBytes lengthBytes consumedBytes true).
Proof.
  intros Hinput Hdomain Hprefix Hheader Hpayload Hnonnegative
    Hbefore Hp Hl Hc Hpv Hlv Hcv Hcandidate Hpath.
  eapply decodeItemLongListReturn;
    [exact Hdomain|exact Hcandidate| |lia|exact Hnonnegative|exact Hpath].
  rewrite Hinput. subst headerLength payloadLength.
  eapply return_800d6b2c_longList; eauto.
  rewrite Hpv. now rewrite Z.add_assoc.
Qed.

Lemma returnExitError args :
  decodeItemC1BDomain args ->
  candidateDecodeItem (decodeItemInputBytes args) = candidateError ->
  runRlpDecodeItem (decodeItemInputBytes args) (decodeItemSailCursor args) =
    Reject RlpDecode ->
  DecodeMeaningModuloKnownBugs args errorEncoding.
Proof.
  intros Hdomain Hcandidate Hreject.
  destruct (return_800d6b04_error (decodeItemInputPointer args)
    (decodeItemInputBytes args) (decodeItemBeforeStorage args)) as
    [Hresult Himage].
  eapply decodeItemErrorReturn; eauto.
Qed.

Print Assumptions returnExitLiteral.
Print Assumptions returnExitShortString.
Print Assumptions returnExitEmptyString.
Print Assumptions returnExitShortList.
Print Assumptions returnExitLongString.
Print Assumptions returnExitLongList.
Print Assumptions returnExitError.
