Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Generated.DecodeItem.Entries.
Require Import ZesuSsz.Automation.Hooks.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.RlpDecodeItem.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Require Import ZesuSsz.Contracts.RlpDecodeItemByteFold.
Require Import ZesuSsz.Contracts.RlpDecodeItemByteFoldBlocks.
Require Import ZesuSsz.Contracts.DecodeItemBranchEntries.
Require Import ZesuSsz.Contracts.DecodeItemReturnFacts.
Require Import ZesuSsz.Contracts.RlpDecodeItemBlockEntries.
Require Import ZesuSsz.Compliance.DecodeItemFoldInitializationWitnesses.
Require Import ZesuSsz.Compliance.DecodeItemCorrectedWitnessSelections.
From Coq Require Import List ZArith.
Open Scope Z_scope.

Lemma decodeItemStringInitializationAnchorCanonical
    `{!islaG Sigma} `{!threadG}
    (args : DecodeItemArgs) (prefix : byte) (rest : list byte)
    (n payloadStart : Z) (lengthBytes frameBytes : list byte) (loaded : bv 64) :
  @ZesuCanonicalAnchor Sigma
    (decodeItemByteFoldStringHeader args n 0 payloadStart lengthBytes frameBytes loaded)
    (decodeItemEntryAt800d6a24 args prefix rest)
    (⌜decodeItemByteFoldFacts args n 0 payloadStart lengthBytes⌝ ∗
     ⌜decodeItemDomainAt (decodeItemReturnAddress args) decodeItemC1BDomain args⌝ ∗
     ⌜decodeItemSavedFrameFacts args frameBytes⌝ ∗
     ⌜decodeItemFoldProvenance args false prefix rest n payloadStart lengthBytes⌝ ∗
     decodeItemByteFoldStringHeader args n 0 payloadStart lengthBytes frameBytes loaded ∗
     decodeItemBranchContinuation args)%I.
Proof. unfold ZesuCanonicalAnchor. exact (decodeItemStringInitializationAnchor args prefix rest n payloadStart lengthBytes frameBytes loaded). Qed.

Lemma decodeItemListInitializationAnchorCanonical
    `{!islaG Sigma} `{!threadG}
    (args : DecodeItemArgs) (prefix : byte) (rest : list byte)
    (n payloadStart : Z) (lengthBytes frameBytes : list byte) (loaded : bv 64) :
  @ZesuCanonicalAnchor Sigma
    (decodeItemByteFoldListHeader args n 0 payloadStart lengthBytes frameBytes loaded)
    (decodeItemEntryAt800d6ac4 args prefix rest)
    (⌜decodeItemByteFoldFacts args n 0 payloadStart lengthBytes⌝ ∗
     ⌜decodeItemDomainAt (decodeItemReturnAddress args) decodeItemC1BDomain args⌝ ∗
     ⌜decodeItemSavedFrameFacts args frameBytes⌝ ∗
     ⌜decodeItemFoldProvenance args true prefix rest n payloadStart lengthBytes⌝ ∗
     decodeItemByteFoldListHeader args n 0 payloadStart lengthBytes frameBytes loaded ∗
     decodeItemBranchContinuation args)%I.
Proof. unfold ZesuCanonicalAnchor. exact (decodeItemListInitializationAnchor args prefix rest n payloadStart lengthBytes frameBytes loaded). Qed.

Lemma decodeItemStringSliceWitnessCanonical
    `{!islaG Sigma} `{!threadG}
    args (prefix : byte) (rest frameBytes : list byte) (oldAcc oldCursor loaded : bv 64) :
  @ZesuCanonicalAnchor Sigma
    (decodeItemFoldInitResources args (bv_unsigned prefix - 183) (decodeItemInputPointer args + 1) (firstn (Z.to_nat (bv_unsigned prefix - 183)) rest)
      frameBytes oldAcc oldCursor loaded)
    (∃ (n payloadStart : Z) (lengthBytes frameBytes : list byte)
       (oldAcc oldCursor loaded : bv 64) (prefix : byte) (rest : list byte),
      decodeItemEntryAt800d6a14 args n payloadStart lengthBytes frameBytes
        oldAcc oldCursor loaded prefix rest)%I
    (⌜decodeItemC1BDomain args /\
      decodeItemFoldProvenance args false prefix rest (bv_unsigned prefix - 183) (decodeItemInputPointer args + 1) (firstn (Z.to_nat (bv_unsigned prefix - 183)) rest) /\
      bv_unsigned (Z_to_bv 64 (bv_unsigned prefix - 183)) < bv_unsigned (Z_to_bv 64 (decodeItemInputLength args)) /\
      decodeItemSavedFrameFacts args frameBytes⌝ ∗
     decodeItemFoldInitResources args (bv_unsigned prefix - 183) (decodeItemInputPointer args + 1) (firstn (Z.to_nat (bv_unsigned prefix - 183)) rest)
       frameBytes oldAcc oldCursor loaded ∗ decodeItemBranchContinuation args)%I.
Proof. unfold ZesuCanonicalAnchor. exact (decodeItemStringSliceWitness args prefix rest frameBytes oldAcc oldCursor loaded). Qed.

Lemma decodeItemListSliceWitnessCanonical
    `{!islaG Sigma} `{!threadG}
    args (prefix : byte) (rest frameBytes : list byte) (oldAcc oldCursor loaded : bv 64) :
  @ZesuCanonicalAnchor Sigma
    (decodeItemFoldInitResources args (bv_unsigned prefix - 247) (decodeItemInputPointer args + 1) (firstn (Z.to_nat (bv_unsigned prefix - 247)) rest)
      frameBytes oldAcc oldCursor loaded)
    (∃ (n payloadStart : Z) (lengthBytes frameBytes : list byte)
       (oldAcc oldCursor loaded : bv 64) (prefix : byte) (rest : list byte),
      decodeItemEntryAt800d6ab4 args n payloadStart lengthBytes frameBytes
        oldAcc oldCursor loaded prefix rest)%I
    (⌜decodeItemC1BDomain args /\
      decodeItemFoldProvenance args true prefix rest (bv_unsigned prefix - 247) (decodeItemInputPointer args + 1) (firstn (Z.to_nat (bv_unsigned prefix - 247)) rest) /\
      bv_unsigned (Z_to_bv 64 (bv_unsigned prefix - 247)) < bv_unsigned (Z_to_bv 64 (decodeItemInputLength args)) /\
      decodeItemSavedFrameFacts args frameBytes⌝ ∗
     decodeItemFoldInitResources args (bv_unsigned prefix - 247) (decodeItemInputPointer args + 1) (firstn (Z.to_nat (bv_unsigned prefix - 247)) rest)
       frameBytes oldAcc oldCursor loaded ∗ decodeItemBranchContinuation args)%I.
Proof. unfold ZesuCanonicalAnchor. exact (decodeItemListSliceWitness args prefix rest frameBytes oldAcc oldCursor loaded). Qed.

Lemma decodeItemStringReturnLengthWitnessCanonical
    `{!islaG Sigma} `{!threadG}
    args (prefix : byte) (rest : list byte) n payloadStart bytes frameBytes (loaded : bv 64) :
  @ZesuCanonicalAnchor Sigma
    (decodeItemFoldCheckedResources args n payloadStart bytes frameBytes loaded)
    (∃ (locals : DecodeItemReturnLocals) (prefix : byte) (rest : list byte)
       (headerLength payloadLength : Z),
      decodeItemEntryAt800d6a40 args locals prefix rest headerLength payloadLength)%I
    (⌜decodeItemDomainAt (decodeItemReturnAddress args) decodeItemC1BDomain args /\
      decodeItemSavedFrameFacts args frameBytes /\
      decodeItemFoldProvenance args false prefix rest n payloadStart bytes /\
      decodeItemByteFoldFacts args n n payloadStart bytes /\
      decodeItemFoldLengthFits args n bytes = true⌝ ∗
     decodeItemFoldCheckedResources args n payloadStart bytes frameBytes loaded ∗
     decodeItemBranchContinuation args)%I.
Proof. unfold ZesuCanonicalAnchor. exact (decodeItemStringReturnLengthWitness args prefix rest n payloadStart bytes frameBytes loaded). Qed.

Lemma decodeItemListReturnLengthWitnessCanonical
    `{!islaG Sigma} `{!threadG}
    args (prefix : byte) (rest : list byte) n payloadStart bytes frameBytes (loaded : bv 64) :
  @ZesuCanonicalAnchor Sigma
    (decodeItemFoldCheckedResources args n payloadStart bytes frameBytes loaded)
    (∃ (locals : DecodeItemReturnLocals) (prefix : byte) (rest : list byte)
       (headerLength payloadLength : Z),
      decodeItemEntryAt800d6b08 args locals prefix rest headerLength payloadLength)%I
    (⌜decodeItemDomainAt (decodeItemReturnAddress args) decodeItemC1BDomain args /\
      decodeItemSavedFrameFacts args frameBytes /\
      decodeItemFoldProvenance args true prefix rest n payloadStart bytes /\
      decodeItemByteFoldFacts args n n payloadStart bytes /\
      decodeItemFoldLengthFits args n bytes = true⌝ ∗
     decodeItemFoldCheckedResources args n payloadStart bytes frameBytes loaded ∗
     decodeItemBranchContinuation args)%I.
Proof. unfold ZesuCanonicalAnchor. exact (decodeItemListReturnLengthWitness args prefix rest n payloadStart bytes frameBytes loaded). Qed.

Print Assumptions decodeItemStringInitializationAnchorCanonical.
Print Assumptions decodeItemListInitializationAnchorCanonical.
Print Assumptions decodeItemStringSliceWitnessCanonical.
Print Assumptions decodeItemListSliceWitnessCanonical.
Print Assumptions decodeItemStringReturnLengthWitnessCanonical.
Print Assumptions decodeItemListReturnLengthWitnessCanonical.
