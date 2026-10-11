Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Require Import ZesuSsz.Automation.Approved.
Require Import ZesuSsz.Compliance.DecodeItemHints.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Automation.BitvectorFacts.
Require Import ZesuSsz.Contracts.DecodeItemBranchEntries.
Require Import ZesuSsz.Contracts.DecodeItemReturnFacts.
Require Import ZesuSsz.Contracts.RlpDecodeItemByteFold.
Require Import ZesuSsz.Compliance.DecodeItemHeaderWitnessFacts.
Require Import ZesuSsz.Compliance.DecodeItemDataWitnessFacts.
From Coq Require Import List ZArith Lia.
Open Scope Z_scope.
Require Import ZesuSsz.Compliance.DecodeItemCorrectedWitnessSelections.
From Coq Require Import ZArith Lia.

(* Retained-context regressions. No repaired native arm is asserted here. *)

Lemma s124_6a08_canonical_witnesses (args : DecodeItemArgs) (frameBytes : list byte) (register : bv 64) (prefix : byte) (rest : list byte) :
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
  payloadLength = RlpDecodeItem.bigEndian lengthBytes.
Proof.
intros Hhead Hlow Hhigh Hvalue Hframe Hdomain Hguard.
pose proof (decodeItemLongStringHeaderWidth prefix (conj Hlow Hhigh)) as Hwidth.
pose proof (decodeItemStringHeaderReadGuardFacts args register prefix Hdomain (conj Hlow Hhigh) Hvalue Hguard) as Hfits.
pose proof (decodeItemStringHeaderProvenanceFacts args prefix rest Hhead (conj Hlow Hhigh)) as Hprovenance.
pose proof (decodeItemHeaderInitialFoldFacts (decodeItemReturnAddress args) args prefix rest (bv_unsigned prefix - 183) Hdomain Hhead Hwidth Hfits) as Hinitial.
pose proof (decodeItemHeaderUnsignedReadGuardFacts (decodeItemReturnAddress args) args (bv_unsigned prefix - 183) Hdomain ltac:(lia) Hfits) as Hunsigned.
split.
{ exact (conj (conj (proj2 Hdomain) (conj Hprovenance (conj Hunsigned Hframe))) (conj (proj1 Hframe) Hinitial)). }
{ exists (bv_unsigned prefix-183), (decodeItemInputPointer args+1),
    (firstn (Z.to_nat (bv_unsigned prefix-183)) rest),
    (1+(bv_unsigned prefix-183)),
    (RlpDecodeItem.bigEndian (firstn (Z.to_nat (bv_unsigned prefix-183)) rest)).
  repeat split; reflexivity. }
Qed.

Lemma s124_6a38_canonical_witnesses
 (args : DecodeItemArgs) (n payloadStart : Z)
 (lengthBytes frameBytes : list byte) (inputPrefix : byte) (rest : list byte) :
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
 ((headerLength+payloadLength) mod RlpDecodeItem.word64Modulus).
Proof.
 intros Hdomain Hprovenance Hframe Hfold Hguard.
 pose proof (decodeItemCompletedFoldFitsGuard args n payloadStart lengthBytes Hfold Hguard) as Hfits.
 pose proof (decodeItemCompletedFoldAcceptedWitnessFacts args false inputPrefix rest n payloadStart lengthBytes Hdomain Hprovenance Hfold Hfits) as Haccepted.
 pose proof (decodeItemCompletedFoldWordValues args n payloadStart lengthBytes Hdomain Hfold) as Hwords.
 destruct Hprovenance as (Hhead & Hclass & Hn & Hstart & Hbytes).
 exists (1+n), (RlpDecodeItem.bigEndian lengthBytes), (firstn (Z.to_nat n) rest).
 exact (conj eq_refl (conj eq_refl (conj eq_refl (conj Hbytes (conj Hstart (conj Hframe (conj Haccepted Hwords))))))).
Qed.

Lemma s124_6aa8_canonical_witnesses (args : DecodeItemArgs) (frameBytes : list byte) (register : bv 64) (prefix : byte) (rest : list byte) :
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
  payloadLength = RlpDecodeItem.bigEndian lengthBytes.
Proof.
intros Hhead Hlow Hhigh Hvalue Hframe Hdomain Hguard.
pose proof (decodeItemLongListHeaderWidth prefix (conj Hlow Hhigh)) as Hwidth.
pose proof (decodeItemListHeaderReadGuardFacts args register prefix Hdomain (conj Hlow Hhigh) Hvalue Hguard) as Hfits.
pose proof (decodeItemListHeaderProvenanceFacts args prefix rest Hhead (conj Hlow Hhigh)) as Hprovenance.
pose proof (decodeItemHeaderInitialFoldFacts (decodeItemReturnAddress args) args prefix rest (bv_unsigned prefix - 247) Hdomain Hhead Hwidth Hfits) as Hinitial.
pose proof (decodeItemHeaderUnsignedReadGuardFacts (decodeItemReturnAddress args) args (bv_unsigned prefix - 247) Hdomain ltac:(lia) Hfits) as Hunsigned.
split.
{ exact (conj (conj (proj2 Hdomain) (conj Hprovenance (conj Hunsigned Hframe))) (conj (proj1 Hframe) Hinitial)). }
{ exists (bv_unsigned prefix-247), (decodeItemInputPointer args+1),
    (firstn (Z.to_nat (bv_unsigned prefix-247)) rest),
    (1+(bv_unsigned prefix-247)),
    (RlpDecodeItem.bigEndian (firstn (Z.to_nat (bv_unsigned prefix-247)) rest)).
  repeat split; reflexivity. }
Qed.

Lemma s124_6ad8_canonical_witnesses
 (args : DecodeItemArgs) (n payloadStart : Z)
 (lengthBytes frameBytes : list byte) (inputPrefix : byte) (rest : list byte) :
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
 ((headerLength+payloadLength) mod RlpDecodeItem.word64Modulus).
Proof.
 intros Hdomain Hprovenance Hframe Hfold Hguard.
 assert (Hnotlt : ~ bv_signed (bv_zero_extend 128 (Z_to_bv 64 (decodeItemInputLength args))) < bv_signed (bv_zero_extend 128 (Z_to_bv 64 (RlpDecodeItem.bigEndian (take (Z.to_nat n) lengthBytes)) + Z_to_bv 64 (n+1)))) by lia.
 pose proof (decodeItemCompletedFoldFitsGuard args n payloadStart lengthBytes Hfold Hnotlt) as Hfits.
 pose proof (decodeItemCompletedFoldAcceptedWitnessFacts args true inputPrefix rest n payloadStart lengthBytes Hdomain Hprovenance Hfold Hfits) as Haccepted.
 pose proof (decodeItemCompletedFoldWordValues args n payloadStart lengthBytes Hdomain Hfold) as Hwords.
 destruct Hprovenance as (Hhead & Hclass & Hn & Hstart & Hbytes).
 exists (1+n), (RlpDecodeItem.bigEndian lengthBytes), (firstn (Z.to_nat n) rest).
 exact (conj eq_refl (conj eq_refl (conj eq_refl (conj Hbytes (conj Hstart (conj Hframe (conj Haccepted Hwords))))))).
Qed.

Lemma s119_literal_committed_witness_conflict args (inputPrefix : byte) (rest : list byte) (b5 : bool) :
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
 False.
Proof.
 intros Hprefix Hp Hl Hnowrap Hreadable Hguard Hfold Hbytes.
 destruct b5; cbn in Hguard, Hfold.
 { rewrite Hbytes in Hfold.
   rewrite -decodeItemStoredWordBytes in Hfold.
   rewrite decodeItemStoredWordValue in Hfold.
   pose proof (decodeItemRawInputPointer args Hp Hl Hnowrap) as Hpointer.
   cbn [defaultMap mapInputBufferAddress mapRamBase] in Hreadable.
   destruct Hreadable as [[Hminimum _]|[Hminimum _]]; lia. }
 { lia. }
Qed.

Lemma s119_successor_committed_witness_conflict args (inputPrefix : byte) (rest : list byte) (b6 : bool) :
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
 False.
Proof.
 intros Hhead Hlower Hupper Hlength Hp Hnowrap Hreadable Hguard Hfold Hbytes.
 destruct b6; cbn in Hguard, Hfold.
 { lia. }
 { rewrite Hbytes in Hfold.
   rewrite -decodeItemStoredWordBytes in Hfold.
   rewrite decodeItemStoredWordValue in Hfold.
   pose proof (decodeItemRawInputSuccessor args inputPrefix rest Hhead Hlength Hp Hnowrap) as Hpointer.
   cbn [defaultMap mapInputBufferAddress mapRamBase] in Hreadable.
   destruct Hreadable as [[Hminimum _]|[Hminimum _]]; lia. }
Qed.
