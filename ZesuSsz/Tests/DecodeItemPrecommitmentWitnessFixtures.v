Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.Approved.
Require Import ZesuSsz.Compliance.DecodeItemHints.
Require Import ZesuSsz.Evidence.DecodeItemPrecommitmentWitnessFixtures.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Require Import ZesuSsz.Contracts.DecodeItemBranchEntries.
Require Import ZesuSsz.Contracts.DecodeItemReturnFacts.
Require Import ZesuSsz.Contracts.RlpDecodeItemByteFold.
From Coq Require Import List ZArith.
Open Scope Z_scope.

Check (s124_6a08_canonical_witnesses : forall (args : DecodeItemArgs) (frameBytes : list byte) (register : bv 64) (prefix : byte) (rest : list byte),
  decodeItemInputHead args prefix rest ->
  184 <= bv_unsigned prefix -> bv_unsigned prefix <= 191 ->
  bv_unsigned register = bv_unsigned prefix ->
  decodeItemSavedFrameFacts args frameBytes ->
  decodeItemDomainAt (decodeItemReturnAddress args) decodeItemC1BDomain args ->
  ~ bv_signed (bv_zero_extend 128 (bv_and (register + 73) 255)) >=
      bv_signed (bv_zero_extend 128 (Z_to_bv 64 (decodeItemInputLength args))) ->
 (  (decodeItemC1BDomain args /\
   decodeItemFoldProvenance args false prefix rest (bv_unsigned prefix - 183) (decodeItemInputPointer args + 1) (firstn (Z.to_nat (bv_unsigned prefix - 183)) rest) /\
   bv_unsigned (Z_to_bv 64 (bv_unsigned prefix - 183)) < bv_unsigned (Z_to_bv 64 (decodeItemInputLength args)) /\
   decodeItemSavedFrameFacts args frameBytes) /\
  (length frameBytes = 16%nat /\ decodeItemByteFoldFacts args (bv_unsigned prefix - 183) 0 (decodeItemInputPointer args + 1) (firstn (Z.to_nat (bv_unsigned prefix - 183)) rest))) /\
  exists n payloadStart lengthBytes headerLength payloadLength,
  n = bv_unsigned prefix - 183 /\
  payloadStart = decodeItemInputPointer args + 1 /\
  lengthBytes = firstn (Z.to_nat n) rest /\
  headerLength = 1+n /\
  payloadLength = RlpDecodeItem.bigEndian lengthBytes).
Print Assumptions s124_6a08_canonical_witnesses.

Check (s124_6a38_canonical_witnesses : forall (args : DecodeItemArgs) (n payloadStart : Z)
 (lengthBytes frameBytes : list byte) (inputPrefix : byte) (rest : list byte),
 decodeItemC1BDomain args ->
 decodeItemFoldProvenance args false inputPrefix rest n payloadStart lengthBytes ->
 decodeItemSavedFrameFacts args frameBytes ->
 decodeItemByteFoldFacts args n n payloadStart lengthBytes ->
 ~ bv_signed (bv_zero_extend 128 (Z_to_bv 64 (decodeItemInputLength args))) <
 bv_signed (bv_zero_extend 128
 (Z_to_bv 64 (RlpDecodeItem.bigEndian (take (Z.to_nat n) lengthBytes)) + Z_to_bv 64 (n+1))) ->
 exists headerLength payloadLength sliceBytes,
 headerLength = 1+n /\
 payloadLength = RlpDecodeItem.bigEndian lengthBytes /\
 sliceBytes = firstn (Z.to_nat n) rest /\
 lengthBytes = sliceBytes /\
 payloadStart = decodeItemInputPointer args+1 /\
 decodeItemSavedFrameFacts args frameBytes /\
 decodeItemLongAcceptedFacts args false headerLength payloadLength /\
 bv_unsigned (Z_to_bv 64 (payloadStart+n)) = decodeItemInputPointer args+headerLength /\
 bv_unsigned (Z_to_bv 64 (RlpDecodeItem.bigEndian lengthBytes)) = payloadLength /\
 bv_unsigned (Z_to_bv 64 (RlpDecodeItem.bigEndian lengthBytes+n+1)) =
 ((headerLength+payloadLength) mod RlpDecodeItem.word64Modulus)).
Print Assumptions s124_6a38_canonical_witnesses.

Check (s124_6aa8_canonical_witnesses : forall (args : DecodeItemArgs) (frameBytes : list byte) (register : bv 64) (prefix : byte) (rest : list byte),
  decodeItemInputHead args prefix rest ->
  248 <= bv_unsigned prefix -> bv_unsigned prefix <= 255 ->
  bv_unsigned register = bv_unsigned prefix ->
  decodeItemSavedFrameFacts args frameBytes ->
  decodeItemDomainAt (decodeItemReturnAddress args) decodeItemC1BDomain args ->
  ~ bv_signed (bv_zero_extend 128 (bv_and (register + 9) 255)) >=
      bv_signed (bv_zero_extend 128 (Z_to_bv 64 (decodeItemInputLength args))) ->
 (  (decodeItemC1BDomain args /\
   decodeItemFoldProvenance args true prefix rest (bv_unsigned prefix - 247) (decodeItemInputPointer args + 1) (firstn (Z.to_nat (bv_unsigned prefix - 247)) rest) /\
   bv_unsigned (Z_to_bv 64 (bv_unsigned prefix - 247)) < bv_unsigned (Z_to_bv 64 (decodeItemInputLength args)) /\
   decodeItemSavedFrameFacts args frameBytes) /\
  (length frameBytes = 16%nat /\ decodeItemByteFoldFacts args (bv_unsigned prefix - 247) 0 (decodeItemInputPointer args + 1) (firstn (Z.to_nat (bv_unsigned prefix - 247)) rest))) /\
  exists n payloadStart lengthBytes headerLength payloadLength,
  n = bv_unsigned prefix - 247 /\
  payloadStart = decodeItemInputPointer args + 1 /\
  lengthBytes = firstn (Z.to_nat n) rest /\
  headerLength = 1+n /\
  payloadLength = RlpDecodeItem.bigEndian lengthBytes).
Print Assumptions s124_6aa8_canonical_witnesses.

Check (s124_6ad8_canonical_witnesses : forall (args : DecodeItemArgs) (n payloadStart : Z)
 (lengthBytes frameBytes : list byte) (inputPrefix : byte) (rest : list byte),
 decodeItemC1BDomain args ->
 decodeItemFoldProvenance args true inputPrefix rest n payloadStart lengthBytes ->
 decodeItemSavedFrameFacts args frameBytes ->
 decodeItemByteFoldFacts args n n payloadStart lengthBytes ->
 bv_signed (bv_zero_extend 128 (Z_to_bv 64 (decodeItemInputLength args))) >=
 bv_signed (bv_zero_extend 128
 (Z_to_bv 64 (RlpDecodeItem.bigEndian (take (Z.to_nat n) lengthBytes)) + Z_to_bv 64 (n+1))) ->
 exists headerLength payloadLength sliceBytes,
 headerLength = 1+n /\
 payloadLength = RlpDecodeItem.bigEndian lengthBytes /\
 sliceBytes = firstn (Z.to_nat n) rest /\
 lengthBytes = sliceBytes /\
 payloadStart = decodeItemInputPointer args+1 /\
 decodeItemSavedFrameFacts args frameBytes /\
 decodeItemLongAcceptedFacts args true headerLength payloadLength /\
 bv_unsigned (Z_to_bv 64 (payloadStart+n)) = decodeItemInputPointer args+headerLength /\
 bv_unsigned (Z_to_bv 64 (RlpDecodeItem.bigEndian lengthBytes)) = payloadLength /\
 bv_unsigned (Z_to_bv 64 (RlpDecodeItem.bigEndian lengthBytes+n+1)) =
 ((headerLength+payloadLength) mod RlpDecodeItem.word64Modulus)).
Print Assumptions s124_6ad8_canonical_witnesses.

Check (s119_literal_committed_witness_conflict : forall args (inputPrefix : byte) (rest : list byte) (b5 : bool),
 bv_unsigned inputPrefix <= 127 ->
 0 <= decodeItemInputPointer args ->
 0 <= decodeItemInputLength args ->
 decodeItemInputPointer args + decodeItemInputLength args < RlpDecodeItem.word64Modulus ->
 ((mapInputBufferAddress defaultMap <= decodeItemInputPointer args /\
   decodeItemInputPointer args + decodeItemInputLength args <= mapInputBufferAddress defaultMap + mapInputCapacity defaultMap) \/
  (mapRamBase defaultMap <= decodeItemInputPointer args /\
   decodeItemInputPointer args + decodeItemInputLength args <= machineRamEnd defaultMap)) ->
 (if b5 then bv_unsigned inputPrefix <= 127 else 129 <= bv_unsigned inputPrefix <= 183) ->
 RlpDecodeItem.littleEndian rest = (if b5 then 1 else bv_unsigned inputPrefix - 128) ->
 rest = AbiBytes.word64Bytes (bv_unsigned (Z_to_bv 64 (decodeItemInputPointer args))) ->
 False).
Print Assumptions s119_literal_committed_witness_conflict.

Check (s119_successor_committed_witness_conflict : forall args (inputPrefix : byte) (rest : list byte) (b6 : bool),
 decodeItemInputHead args inputPrefix rest ->
 129 <= bv_unsigned inputPrefix ->
 bv_unsigned inputPrefix <= 183 ->
 decodeItemInputLength args = Z.of_nat (length (decodeItemInputBytes args)) ->
 0 <= decodeItemInputPointer args ->
 decodeItemInputPointer args + decodeItemInputLength args < RlpDecodeItem.word64Modulus ->
 ((mapInputBufferAddress defaultMap <= decodeItemInputPointer args /\
   decodeItemInputPointer args + decodeItemInputLength args <= mapInputBufferAddress defaultMap + mapInputCapacity defaultMap) \/
  (mapRamBase defaultMap <= decodeItemInputPointer args /\
   decodeItemInputPointer args + decodeItemInputLength args <= machineRamEnd defaultMap)) ->
 (if b6 then bv_unsigned inputPrefix <= 127 else 129 <= bv_unsigned inputPrefix <= 183) ->
 RlpDecodeItem.littleEndian rest = (if b6 then 1 else bv_unsigned inputPrefix - 128) ->
 rest = AbiBytes.word64Bytes (bv_unsigned (bv_add (Z_to_bv 64 (decodeItemInputPointer args)) 1)) ->
 False).
Print Assumptions s119_successor_committed_witness_conflict.
