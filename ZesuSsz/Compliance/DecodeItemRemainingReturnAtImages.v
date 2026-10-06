Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.RlpDecodeItem.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Require Import ZesuSsz.Contracts.RlpDecodeItemSchema.
Require Import ZesuSsz.Contracts.RlpDecodeItemBlockEntries.
Require Import ZesuSsz.Contracts.DecodeItemReturnFacts.
Require Import ZesuSsz.Contracts.AbiBytes.
Require Import ZesuSsz.Contracts.RlpDecodeItemReturnImageDef.
Require Import ZesuSsz.Compliance.DecodeItemReturnExitResources.
Open Scope Z_scope.

Lemma decodeItemReturnAt698cImage args locals (lengthBytes : list byte)
    (inputPrefix : byte) (isLiteral : bool) after :
  decodeItemDomainAt (decodeItemReturnAddress args) decodeItemC1BDomain args ->
  (if isLiteral then bv_unsigned inputPrefix <= 127
   else 129 <= bv_unsigned inputPrefix <= 183) ->
  decodeItemAcceptedFacts args false (if isLiteral then 0 else 1)
    (if isLiteral then 1 else bv_unsigned inputPrefix - 128) ->
  encodeResult (decodeItemInputPointer args) (decodeItemInputBytes args)
    (decodeItemBeforeStorage args) after
    (candidateSuccess false (if isLiteral then 0 else 1)
      (if isLiteral then 1 else bv_unsigned inputPrefix - 128)) ->
  after = decodeItemOkBytes (decodeItemBeforeStorage args)
      (word64Bytes (bv_unsigned (returnA1 locals)))
      (word64Bytes (littleEndian lengthBytes))
      (word64Bytes (bv_unsigned (returnA2 locals))) false ->
  decodeItemDomainAt (decodeItemReturnAddress args) decodeItemC1BDomain args /\
  DecodeMeaningModuloKnownBugs args (decodeItemOkBytes (decodeItemBeforeStorage args)
      (word64Bytes (bv_unsigned (returnA1 locals)))
      (word64Bytes (littleEndian lengthBytes))
      (word64Bytes (bv_unsigned (returnA2 locals))) false).
Proof.
  intros Hdomain Hclass Haccepted Himage ->. split; [exact Hdomain |].
  destruct isLiteral.
  - eapply decodeItemLiteralPostMeaning; [exact (proj2 Hdomain) | exact Haccepted | exact Himage].
  - eapply decodeItemShortStringPostMeaning;
      [exact (proj2 Hdomain) | exact Haccepted | exact Himage | lia |].
    unfold word64Modulus. lia.
Qed.

Lemma decodeItemReturnAt6a40Image args locals (inputPrefix : byte)
    headerLength payloadLength after :
  decodeItemDomainAt (decodeItemReturnAddress args) decodeItemC1BDomain args ->
  184 <= bv_unsigned inputPrefix <= 191 ->
  headerLength = 1 + (bv_unsigned inputPrefix - 183) ->
  0 <= payloadLength ->
  decodeItemLongAcceptedFacts args false headerLength payloadLength ->
  encodeResult (decodeItemInputPointer args) (decodeItemInputBytes args)
    (decodeItemBeforeStorage args) after
    (candidateSuccess false headerLength payloadLength) ->
  after = decodeItemOkBytes (decodeItemBeforeStorage args)
      (word64Bytes (bv_unsigned (returnA1 locals)))
      (word64Bytes (bv_unsigned (returnA3 locals)))
      (word64Bytes (bv_unsigned (returnA4 locals))) false ->
  decodeItemDomainAt (decodeItemReturnAddress args) decodeItemC1BDomain args /\
  DecodeMeaningModuloKnownBugs args (decodeItemOkBytes (decodeItemBeforeStorage args)
      (word64Bytes (bv_unsigned (returnA1 locals)))
      (word64Bytes (bv_unsigned (returnA3 locals)))
      (word64Bytes (bv_unsigned (returnA4 locals))) false).
Proof.
  intros Hdomain Hclass Hheader Hnonnegative Haccepted Himage ->.
  split; [exact Hdomain |].
  eapply decodeItemLongStringPostMeaning;
    [exact (proj2 Hdomain) | exact Haccepted | exact Himage | lia | exact Hnonnegative].
Qed.

Lemma decodeItemReturnAt6b08Image args locals (inputPrefix : byte)
    headerLength payloadLength after :
  decodeItemDomainAt (decodeItemReturnAddress args) decodeItemC1BDomain args ->
  248 <= bv_unsigned inputPrefix <= 255 ->
  headerLength = 1 + (bv_unsigned inputPrefix - 247) ->
  0 <= payloadLength ->
  decodeItemLongAcceptedFacts args true headerLength payloadLength ->
  encodeResult (decodeItemInputPointer args) (decodeItemInputBytes args)
    (decodeItemBeforeStorage args) after
    (candidateSuccess true headerLength payloadLength) ->
  after = decodeItemOkBytes (decodeItemBeforeStorage args)
      (word64Bytes (bv_unsigned (returnA1 locals)))
      (word64Bytes (bv_unsigned (returnA3 locals)))
      (word64Bytes (bv_unsigned (returnA4 locals))) true ->
  decodeItemDomainAt (decodeItemReturnAddress args) decodeItemC1BDomain args /\
  DecodeMeaningModuloKnownBugs args (decodeItemOkBytes (decodeItemBeforeStorage args)
      (word64Bytes (bv_unsigned (returnA1 locals)))
      (word64Bytes (bv_unsigned (returnA3 locals)))
      (word64Bytes (bv_unsigned (returnA4 locals))) true).
Proof.
  intros Hdomain Hclass Hheader Hnonnegative Haccepted Himage ->.
  split; [exact Hdomain |].
  eapply decodeItemLongListPostMeaning;
    [exact (proj2 Hdomain) | exact Haccepted | exact Himage | lia | exact Hnonnegative].
Qed.

Print Assumptions decodeItemReturnAt698cImage.
Print Assumptions decodeItemReturnAt6a40Image.
Print Assumptions decodeItemReturnAt6b08Image.
