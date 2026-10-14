Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Compliance.DecodeItemUnfoldRegistrations.
Require Import ZesuSsz.Compliance.ByteFold.
Require Import isla.riscv64.riscv64.
From Coq Require Import List ZArith Lia.
Require Import ZesuSsz.Contracts.RlpDecodeItem.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Require Import ZesuSsz.Contracts.RlpDecodeItemByteFold.
Require Import ZesuSsz.Contracts.RlpDecodeItemByteFoldBlocks.
Require Import ZesuSsz.Contracts.RlpDecodeItemFoldEntries.
Require Import ZesuSsz.Contracts.DecodeItemBranchEntries.
Require Import ZesuSsz.Contracts.DecodeItemReturnFacts.
Require Import ZesuSsz.Contracts.RlpDecodeItemBlockEntries.
Require Import ZesuSsz.Contracts.ResultImage.
Require Import ZesuSsz.Compliance.DecodeItemHeaderWitnessFacts.
Require Import ZesuSsz.Compliance.DecodeItemFoldBackEdgeWitnesses.
Require Import ZesuSsz.Proofs.DecodeItem.ByteFoldPure.
Require Import ZesuSsz.Automation.Switches.PureFactHints.
Import ListNotations.
Open Scope Z_scope.

Require Import ZesuSsz.Compliance.DecodeItemCorrectedWitnessSelections.
Example decodeItemStringSliceWitnessActivation
    `{!islaG Sigma} `{!threadG}
    args (prefix : byte) (rest frameBytes : list byte) (oldAcc oldCursor loaded : bv 64)  :
  ⊢ ((⌜decodeItemC1BDomain args /\
      decodeItemFoldProvenance args false prefix rest (bv_unsigned prefix - 183) (decodeItemInputPointer args + 1) (firstn (Z.to_nat (bv_unsigned prefix - 183)) rest) /\
      bv_unsigned (Z_to_bv 64 (bv_unsigned prefix - 183)) < bv_unsigned (Z_to_bv 64 (decodeItemInputLength args)) /\
      decodeItemSavedFrameFacts args frameBytes⌝ ∗
     decodeItemFoldInitResources args (bv_unsigned prefix - 183) (decodeItemInputPointer args + 1) (firstn (Z.to_nat (bv_unsigned prefix - 183)) rest)
       frameBytes oldAcc oldCursor loaded ∗ decodeItemBranchContinuation args) -∗ (∃ (n payloadStart : Z) (lengthBytes frameBytes : list byte)
       (oldAcc oldCursor loaded : bv 64) (prefix : byte) (rest : list byte),
      decodeItemEntryAt800d6a14 args n payloadStart lengthBytes frameBytes
        oldAcc oldCursor loaded prefix rest)%I)%I.
Proof. iIntros "Hsource". iDestruct "Hsource" as "[%Hfacts [Hanchor Hcont]]". zesu_pure_fact_hints_if_enabled. iFrame. iPureIntro. exact Hfacts. Qed.

Example decodeItemListSliceWitnessActivation
    `{!islaG Sigma} `{!threadG}
    args (prefix : byte) (rest frameBytes : list byte) (oldAcc oldCursor loaded : bv 64)  :
  ⊢ ((⌜decodeItemC1BDomain args /\
      decodeItemFoldProvenance args true prefix rest (bv_unsigned prefix - 247) (decodeItemInputPointer args + 1) (firstn (Z.to_nat (bv_unsigned prefix - 247)) rest) /\
      bv_unsigned (Z_to_bv 64 (bv_unsigned prefix - 247)) < bv_unsigned (Z_to_bv 64 (decodeItemInputLength args)) /\
      decodeItemSavedFrameFacts args frameBytes⌝ ∗
     decodeItemFoldInitResources args (bv_unsigned prefix - 247) (decodeItemInputPointer args + 1) (firstn (Z.to_nat (bv_unsigned prefix - 247)) rest)
       frameBytes oldAcc oldCursor loaded ∗ decodeItemBranchContinuation args) -∗ (∃ (n payloadStart : Z) (lengthBytes frameBytes : list byte)
       (oldAcc oldCursor loaded : bv 64) (prefix : byte) (rest : list byte),
      decodeItemEntryAt800d6ab4 args n payloadStart lengthBytes frameBytes
        oldAcc oldCursor loaded prefix rest)%I)%I.
Proof. iIntros "Hsource". iDestruct "Hsource" as "[%Hfacts [Hanchor Hcont]]". zesu_pure_fact_hints_if_enabled. iFrame. iPureIntro. exact Hfacts. Qed.

Example decodeItemStringReturnLengthWitnessActivation
    `{!islaG Sigma} `{!threadG}
    args (prefix : byte) (rest : list byte) n payloadStart bytes frameBytes (loaded : bv 64)  :
  ⊢ ((⌜decodeItemDomainAt (decodeItemReturnAddress args) decodeItemC1BDomain args /\
      decodeItemSavedFrameFacts args frameBytes /\
      decodeItemFoldProvenance args false prefix rest n payloadStart bytes /\
      decodeItemByteFoldFacts args n n payloadStart bytes /\
      decodeItemFoldLengthFits args n bytes = true⌝ ∗
     decodeItemFoldCheckedResources args n payloadStart bytes frameBytes loaded ∗
     decodeItemBranchContinuation args) -∗ (∃ (locals : DecodeItemReturnLocals) (prefix : byte) (rest : list byte)
       (headerLength payloadLength : Z),
      decodeItemEntryAt800d6a40 args locals prefix rest headerLength payloadLength)%I)%I.
Proof. iIntros "Hsource". iDestruct "Hsource" as "[%Hfacts [Hanchor Hcont]]". pose proof Hfacts as (_ & _ & Hprovenance & _). zesu_pure_fact_hints_if_enabled. iFrame. iPureIntro. exact Hfacts. Qed.

Example decodeItemListReturnLengthWitnessActivation
    `{!islaG Sigma} `{!threadG}
    args (prefix : byte) (rest : list byte) n payloadStart bytes frameBytes (loaded : bv 64)  :
  ⊢ ((⌜decodeItemDomainAt (decodeItemReturnAddress args) decodeItemC1BDomain args /\
      decodeItemSavedFrameFacts args frameBytes /\
      decodeItemFoldProvenance args true prefix rest n payloadStart bytes /\
      decodeItemByteFoldFacts args n n payloadStart bytes /\
      decodeItemFoldLengthFits args n bytes = true⌝ ∗
     decodeItemFoldCheckedResources args n payloadStart bytes frameBytes loaded ∗
     decodeItemBranchContinuation args) -∗ (∃ (locals : DecodeItemReturnLocals) (prefix : byte) (rest : list byte)
       (headerLength payloadLength : Z),
      decodeItemEntryAt800d6b08 args locals prefix rest headerLength payloadLength)%I)%I.
Proof. iIntros "Hsource". iDestruct "Hsource" as "[%Hfacts [Hanchor Hcont]]". pose proof Hfacts as (_ & _ & Hprovenance & _). zesu_pure_fact_hints_if_enabled. iFrame. iPureIntro. exact Hfacts. Qed.

Example decodeItem6a24ArrayIndexActivation `{!islaG Sigma}
    args n i payloadStart bytes (continuation : nat -> iProp Sigma) :
  decodeItemByteFoldFacts args n i payloadStart bytes ->
  ⊢ (continuation (Z.to_nat (1 + i)) -∗
    ∃ index : nat, ⌜Z.of_nat index =
      (payloadStart + i + 0 - decodeItemInputPointer args) `div` 1⌝ ∗ continuation index)%I.
Proof.
  intros Hfold. iIntros "Hcontinuation".
  zesu_pure_fact_hints_if_enabled. iFrame. iPureIntro. exact Hfold.
Qed.

Example decodeItem6a24SteppedCursorActivation args n i payloadStart bytes :
  decodeItemByteFoldFacts args n i payloadStart bytes ->
  (Z_to_bv 64 (payloadStart + i) + 1)%bv = Z_to_bv 64 (payloadStart + (i + 1)).
Proof. intros Hfold. zesu_pure_fact_hints_if_enabled. Qed.

Example decodeItem6a24SteppedAccumulatorActivation args n i payloadStart bytes next :
  decodeItemByteFoldFacts args n i payloadStart bytes -> i < n ->
  nth_error (decodeItemInputBytes args) (Z.to_nat (1 + i)) = Some next ->
  bv_or (Z_to_bv 64 (bigEndian (firstn (Z.to_nat i) bytes)) ≪ 8)
    (bv_zero_extend 64 next) = Z_to_bv 64 (bigEndian (firstn (Z.to_nat (i + 1)) bytes)).
Proof. intros Hfold Hguard Hnext. zesu_pure_fact_hints_if_enabled. Qed.

Example decodeItem6ac4ArrayIndexActivation `{!islaG Sigma}
    args n i payloadStart bytes (continuation : nat -> iProp Sigma) :
  decodeItemByteFoldFacts args n i payloadStart bytes ->
  ⊢ (continuation (Z.to_nat (1 + i)) -∗
    ∃ index : nat, ⌜Z.of_nat index =
      (payloadStart + i + 0 - decodeItemInputPointer args) `div` 1⌝ ∗ continuation index)%I.
Proof.
  intros Hfold. iIntros "Hcontinuation".
  zesu_pure_fact_hints_if_enabled. iFrame. iPureIntro. exact Hfold.
Qed.

Example decodeItem6ac4SteppedCursorActivation args n i payloadStart bytes :
  decodeItemByteFoldFacts args n i payloadStart bytes ->
  (Z_to_bv 64 (payloadStart + i) + 1)%bv = Z_to_bv 64 (payloadStart + (i + 1)).
Proof. intros Hfold. zesu_pure_fact_hints_if_enabled. Qed.

Example decodeItem6ac4SteppedAccumulatorActivation args n i payloadStart bytes next :
  decodeItemByteFoldFacts args n i payloadStart bytes -> i < n ->
  nth_error (decodeItemInputBytes args) (Z.to_nat (1 + i)) = Some next ->
  bv_or (Z_to_bv 64 (bigEndian (firstn (Z.to_nat i) bytes)) ≪ 8)
    (bv_zero_extend 64 next) = Z_to_bv 64 (bigEndian (firstn (Z.to_nat (i + 1)) bytes)).
Proof. intros Hfold Hguard Hnext. zesu_pure_fact_hints_if_enabled. Qed.


Print Assumptions decodeItemStringSliceWitnessActivation.
Print Assumptions decodeItemListSliceWitnessActivation.
Print Assumptions decodeItemStringReturnLengthWitnessActivation.
Print Assumptions decodeItemListReturnLengthWitnessActivation.
Print Assumptions decodeItem6a24ArrayIndexActivation.
Print Assumptions decodeItem6a24SteppedCursorActivation.
Print Assumptions decodeItem6a24SteppedAccumulatorActivation.
Print Assumptions decodeItem6ac4ArrayIndexActivation.
Print Assumptions decodeItem6ac4SteppedCursorActivation.
Print Assumptions decodeItem6ac4SteppedAccumulatorActivation.
