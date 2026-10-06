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

Require Import ZesuSsz.Compliance.DecodeItemRemainingReturnAtImages.

Example decodeItemReturnAt698cImageFixture args locals (lengthBytes : list byte)
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
Proof. apply decodeItemReturnAt698cImage. Qed.

Example decodeItemReturnAt6a40ImageFixture args locals (inputPrefix : byte)
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
Proof. apply decodeItemReturnAt6a40Image. Qed.

Example decodeItemReturnAt6b08ImageFixture args locals (inputPrefix : byte)
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
Proof. apply decodeItemReturnAt6b08Image. Qed.

