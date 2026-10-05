Require Import ZesuSsz.Automation.All.
From Coq Require Import List ZArith Lia.
From stdpp Require Import bitvector.definitions.
Require Import ZesuSsz.Contracts.AbiBytes.
Require Import ZesuSsz.Contracts.RlpDecodeItem.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Require Import ZesuSsz.Contracts.RlpDecodeItemSchema.
Require Import ZesuSsz.Contracts.RlpDecodeItemReturnImageDef.
Require Import ZesuSsz.Contracts.DecodeItemReturnFacts.
Require Import ZesuSsz.Compliance.DecodeItemPathAgreement.
Require Import ZesuSsz.Compliance.DecodeItemReturnExitResources.
Require Import ZesuSsz.Compliance.DecodeItemReturnExitPure.
Require Import ZesuSsz.Compliance.DecodeItemSailIntroduction.
Require Import ZesuSsz.Compliance.DecodeItemSailFold.
Open Scope Z_scope.

(* These fixtures use branch guards and the designed output images.
   They do not assume a Sail outcome or a semantic conclusion. *)
Example decodeItemLiteralSemanticFixture args prefix rest :
  decodeItemC1BDomain args -> decodeItemInputHead args prefix rest ->
  bv_unsigned prefix <= 127 ->
  encodeResult (decodeItemInputPointer args) (decodeItemInputBytes args)
    (decodeItemBeforeStorage args)
    (decodeItemOkBytes (decodeItemBeforeStorage args)
      (word64Bytes (decodeItemInputPointer args)) (word64Bytes 1) (word64Bytes 1) false)
    (candidateSuccess false 0 1) ->
  DecodeMeaningModuloKnownBugs args
    (decodeItemOkBytes (decodeItemBeforeStorage args)
      (word64Bytes (decodeItemInputPointer args)) (word64Bytes 1) (word64Bytes 1) false).
Proof.
  intros Hdomain Hinput Hclass Himage.
  eapply decodeItemLiteralPostMeaning; eauto using decodeItemLiteralAccepted.
Qed.

Example decodeItemEmptySemanticFixture args prefix rest :
  decodeItemC1BDomain args -> decodeItemInputHead args prefix rest ->
  bv_unsigned prefix = 128 ->
  encodeResult (decodeItemInputPointer args) (decodeItemInputBytes args)
    (decodeItemBeforeStorage args)
    (decodeItemOkBytes (decodeItemBeforeStorage args)
      (word64Bytes 1) (word64Bytes 0) (word64Bytes 1) false)
    (candidateSuccess false 1 0) ->
  DecodeMeaningModuloKnownBugs args
    (decodeItemOkBytes (decodeItemBeforeStorage args)
      (word64Bytes 1) (word64Bytes 0) (word64Bytes 1) false).
Proof.
  intros Hdomain Hinput Hclass Himage.
  eapply decodeItemEmptyStringPostMeaning; eauto using decodeItemEmptyAccepted.
Qed.

Example decodeItemShortStringSemanticFixture args prefix rest :
  decodeItemC1BDomain args -> decodeItemInputHead args prefix rest ->
  129 <= bv_unsigned prefix <= 183 ->
  1 + (bv_unsigned prefix - 128) <= Z.of_nat (length (decodeItemInputBytes args)) ->
  encodeResult (decodeItemInputPointer args) (decodeItemInputBytes args)
    (decodeItemBeforeStorage args)
    (decodeItemOkBytes (decodeItemBeforeStorage args)
      (word64Bytes (decodeItemInputPointer args + 1))
      (word64Bytes (bv_unsigned prefix - 128))
      (word64Bytes (1 + (bv_unsigned prefix - 128))) false)
    (candidateSuccess false 1 (bv_unsigned prefix - 128)) ->
  DecodeMeaningModuloKnownBugs args
    (decodeItemOkBytes (decodeItemBeforeStorage args)
      (word64Bytes (decodeItemInputPointer args + 1))
      (word64Bytes (bv_unsigned prefix - 128))
      (word64Bytes (1 + (bv_unsigned prefix - 128))) false).
Proof.
  intros Hdomain Hinput Hclass Hfits Himage.
  eapply decodeItemShortStringPostMeaning; eauto using decodeItemShortStringAccepted;
    unfold word64Modulus; lia.
Qed.

Example decodeItemShortListSemanticFixture args prefix rest :
  decodeItemC1BDomain args -> decodeItemInputHead args prefix rest ->
  192 <= bv_unsigned prefix <= 247 ->
  1 + (bv_unsigned prefix - 192) <= Z.of_nat (length (decodeItemInputBytes args)) ->
  encodeResult (decodeItemInputPointer args) (decodeItemInputBytes args)
    (decodeItemBeforeStorage args)
    (decodeItemOkBytes (decodeItemBeforeStorage args)
      (word64Bytes (decodeItemInputPointer args + 1))
      (word64Bytes (bv_unsigned prefix - 192))
      (word64Bytes (1 + (bv_unsigned prefix - 192))) true)
    (candidateSuccess true 1 (bv_unsigned prefix - 192)) ->
  DecodeMeaningModuloKnownBugs args
    (decodeItemOkBytes (decodeItemBeforeStorage args)
      (word64Bytes (decodeItemInputPointer args + 1))
      (word64Bytes (bv_unsigned prefix - 192))
      (word64Bytes (1 + (bv_unsigned prefix - 192))) true).
Proof.
  intros Hdomain Hinput Hclass Hfits Himage.
  eapply decodeItemShortListPostMeaning; eauto using decodeItemShortListAccepted;
    unfold word64Modulus; lia.
Qed.

Example decodeItemLongStringSemanticFixture args prefix rest n payloadStart lengthBytes :
  decodeItemC1BDomain args ->
  decodeItemFoldProvenance args false prefix rest n payloadStart lengthBytes ->
  1 + n <= Z.of_nat (length (decodeItemInputBytes args)) ->
  (1 + n + bigEndian lengthBytes) mod word64Modulus <=
    Z.of_nat (length (decodeItemInputBytes args)) ->
  encodeResult (decodeItemInputPointer args) (decodeItemInputBytes args)
    (decodeItemBeforeStorage args)
    (decodeItemOkBytes (decodeItemBeforeStorage args)
      (word64Bytes (decodeItemInputPointer args + (1 + n)))
      (word64Bytes (bigEndian lengthBytes))
      (word64Bytes ((1 + n + bigEndian lengthBytes) mod word64Modulus)) false)
    (candidateSuccess false (1 + n) (bigEndian lengthBytes)) ->
  DecodeMeaningModuloKnownBugs args
    (decodeItemOkBytes (decodeItemBeforeStorage args)
      (word64Bytes (decodeItemInputPointer args + (1 + n)))
      (word64Bytes (bigEndian lengthBytes))
      (word64Bytes ((1 + n + bigEndian lengthBytes) mod word64Modulus)) false).
Proof.
  intros Hdomain Hprovenance Hheader Hfits Himage.
  eapply decodeItemLongStringPostMeaning; eauto using decodeItemLongStringAccepted,
    decodeItemBigEndianNonnegative.
  destruct Hprovenance as (_ & Hclass & Hn & _). cbn in Hclass. cbn in Hn. lia.
Qed.

Example decodeItemLongListSemanticFixture args prefix rest n payloadStart lengthBytes :
  decodeItemC1BDomain args ->
  decodeItemFoldProvenance args true prefix rest n payloadStart lengthBytes ->
  1 + n <= Z.of_nat (length (decodeItemInputBytes args)) ->
  (1 + n + bigEndian lengthBytes) mod word64Modulus <=
    Z.of_nat (length (decodeItemInputBytes args)) ->
  encodeResult (decodeItemInputPointer args) (decodeItemInputBytes args)
    (decodeItemBeforeStorage args)
    (decodeItemOkBytes (decodeItemBeforeStorage args)
      (word64Bytes (decodeItemInputPointer args + (1 + n)))
      (word64Bytes (bigEndian lengthBytes))
      (word64Bytes ((1 + n + bigEndian lengthBytes) mod word64Modulus)) true)
    (candidateSuccess true (1 + n) (bigEndian lengthBytes)) ->
  DecodeMeaningModuloKnownBugs args
    (decodeItemOkBytes (decodeItemBeforeStorage args)
      (word64Bytes (decodeItemInputPointer args + (1 + n)))
      (word64Bytes (bigEndian lengthBytes))
      (word64Bytes ((1 + n + bigEndian lengthBytes) mod word64Modulus)) true).
Proof.
  intros Hdomain Hprovenance Hheader Hfits Himage.
  eapply decodeItemLongListPostMeaning; eauto using decodeItemLongListAccepted,
    decodeItemBigEndianNonnegative.
  destruct Hprovenance as (_ & Hclass & Hn & _). cbn in Hclass. cbn in Hn. lia.
Qed.

Example decodeItemErrorSemanticFixture args :
  decodeItemC1BDomain args -> decodeItemRejectedFacts args ->
  DecodeMeaningModuloKnownBugs args errorEncoding.
Proof.
  intros Hdomain [Hcandidate Hreject]. eapply returnExitError; eauto.
Qed.

Print Assumptions decodeItemLiteralSemanticFixture.
Print Assumptions decodeItemEmptySemanticFixture.
Print Assumptions decodeItemShortStringSemanticFixture.
Print Assumptions decodeItemShortListSemanticFixture.
Print Assumptions decodeItemLongStringSemanticFixture.
Print Assumptions decodeItemLongListSemanticFixture.
Print Assumptions decodeItemErrorSemanticFixture.
