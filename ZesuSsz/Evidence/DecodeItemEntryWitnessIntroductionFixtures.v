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
Require Import ZesuSsz.Contracts.DecodeItemFrameImage.

Lemma decodeItemLiteralEntryFactsHintFixture `{!islaG Sigma} `{!threadG}
 args (frameBytes : list byte) (x13 : bv 64) (prefix : byte) (rest : list byte) :
 decodeItemEntryAt800d697c args frameBytes x13 prefix rest ⊢
 ⌜ exists (pointerBytes lengthBytes : list byte) (headerLength payloadLength : Z),
 pointerBytes = bv_to_little_endian 8 8 (bv_unsigned (Z_to_bv 64 (decodeItemInputPointer args))) /\
 lengthBytes = bv_to_little_endian 8 8 (bv_unsigned (Z_to_bv 64 1)) /\
 headerLength = 0 /\ payloadLength = 1 /\
 RlpDecodeItem.littleEndian pointerBytes = Z.add (decodeItemInputPointer args) headerLength /\
 RlpDecodeItem.littleEndian lengthBytes = payloadLength /\
 decodeItemAcceptedFacts args false headerLength payloadLength /\
 decodeItemInputHead args prefix rest /\ decodeItemSavedFrameFacts args frameBytes⌝.
Proof.
  iIntros "Hentry".
  zesu_pure_fact_hints_if_enabled.
  iExact "Hentry".
Qed.
Print Assumptions decodeItemLiteralEntryFactsHintFixture.

Lemma decodeItemShortStringEntryFactsHintFixture `{!islaG Sigma} `{!threadG}
 args (frameBytes : list byte) (x13 : bv 64) (prefix : byte) (rest : list byte) :
 decodeItemEntryAt800d69e8 args frameBytes x13 prefix rest ⊢
 ⌜ exists (pointerBytes lengthBytes : list byte) (headerLength payloadLength : Z),
 pointerBytes = bv_to_little_endian 8 8 (bv_unsigned (bv_add (Z_to_bv 64 (decodeItemInputPointer args)) 1)) /\
 lengthBytes = bv_to_little_endian 8 8 (bv_unsigned x13) /\
 headerLength = 1 /\ payloadLength = Z.sub (bv_unsigned prefix) 128 /\
 RlpDecodeItem.littleEndian pointerBytes = Z.add (decodeItemInputPointer args) headerLength /\
 RlpDecodeItem.littleEndian lengthBytes = payloadLength /\
 decodeItemAcceptedFacts args false headerLength payloadLength /\
 decodeItemInputHead args prefix rest /\ decodeItemSavedFrameFacts args frameBytes⌝.
Proof.
  iIntros "Hentry".
  zesu_pure_fact_hints_if_enabled.
  iExact "Hentry".
Qed.
Print Assumptions decodeItemShortStringEntryFactsHintFixture.

Lemma decodeItemCanonicalEntryFrameFactsHintFixture `{!islaG Sigma} `{!threadG}
 returnAddress args :
 decodeItemEntryAt800d6960 returnAddress args ⊢
 ⌜decodeItemSavedFrameFacts args
 (List.app (bv_to_little_endian 8 8 (bv_unsigned (decodeItemSavedFramePointer args)))
  (bv_to_little_endian 8 8 (bv_unsigned (Z_to_bv 64 (decodeItemReturnAddress args)))))⌝.
Proof.
  iIntros "Hentry".
  zesu_pure_fact_hints_if_enabled.
  iExact "Hentry".
Qed.
Print Assumptions decodeItemCanonicalEntryFrameFactsHintFixture.

