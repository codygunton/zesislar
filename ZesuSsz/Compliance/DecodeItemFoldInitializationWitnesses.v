Require Import ZesuSsz.Automation.All.
From Coq Require Import ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Require Import ZesuSsz.Compliance.DecodeItemJoinTransferPure.
Require Import ZesuSsz.Contracts.RlpDecodeItemByteFold.
Require Import ZesuSsz.Contracts.RlpDecodeItemFoldEntries.
Require Import ZesuSsz.Contracts.DecodeItemReturnFacts.
Require Import ZesuSsz.Contracts.DecodeItemBranchEntries.
Require Import ZesuSsz.Automation.Switches.PureFactHints.
Open Scope Z_scope.

Lemma decodeItemStringInitializationHeaderIntro `{!islaG Sigma} `{!threadG}
    (args : DecodeItemArgs) (prefix : byte) (rest : list byte)
    (n payloadStart : Z) (lengthBytes frameBytes : list byte) (loaded : bv 64) :
  decodeItemByteFoldFacts args n 0 payloadStart lengthBytes ->
  decodeItemDomainAt (decodeItemReturnAddress args) decodeItemC1BDomain args ->
  decodeItemSavedFrameFacts args frameBytes ->
  decodeItemFoldProvenance args false prefix rest n payloadStart lengthBytes ->
  ⊢ (decodeItemByteFoldStringHeader args n 0 payloadStart lengthBytes frameBytes loaded ∗
     decodeItemBranchContinuation args -∗ decodeItemEntryAt800d6a24 args prefix rest)%I.
Proof.
  intros Hfold Hdomain Hframe Hprovenance.
  exact (decodeItemStringHeaderIntro args prefix rest n 0 payloadStart
    lengthBytes frameBytes loaded
    (decodeItemByteFoldFirstGuard args n payloadStart lengthBytes Hfold)
    Hdomain Hframe Hprovenance).
Qed.

Print Assumptions decodeItemStringInitializationHeaderIntro.

Lemma decodeItemListInitializationHeaderIntro `{!islaG Sigma} `{!threadG}
    (args : DecodeItemArgs) (prefix : byte) (rest : list byte)
    (n payloadStart : Z) (lengthBytes frameBytes : list byte) (loaded : bv 64) :
  decodeItemByteFoldFacts args n 0 payloadStart lengthBytes ->
  decodeItemDomainAt (decodeItemReturnAddress args) decodeItemC1BDomain args ->
  decodeItemSavedFrameFacts args frameBytes ->
  decodeItemFoldProvenance args true prefix rest n payloadStart lengthBytes ->
  ⊢ (decodeItemByteFoldListHeader args n 0 payloadStart lengthBytes frameBytes loaded ∗
     decodeItemBranchContinuation args -∗ decodeItemEntryAt800d6ac4 args prefix rest)%I.
Proof.
  intros Hfold Hdomain Hframe Hprovenance.
  exact (decodeItemListHeaderIntro args prefix rest n 0 payloadStart
    lengthBytes frameBytes loaded
    (decodeItemByteFoldFirstGuard args n payloadStart lengthBytes Hfold)
    Hdomain Hframe Hprovenance).
Qed.

Print Assumptions decodeItemListInitializationHeaderIntro.

#[export] Instance decodeItemStringInitializationWitness
    `{!islaG Sigma} `{!threadG}
    (args : DecodeItemArgs) (prefix : byte) (rest : list byte)
    (n payloadStart : Z) (lengthBytes frameBytes : list byte) (loaded : bv 64) :
  @ZesuPureFactIntro Sigma (decodeItemEntryAt800d6a24 args prefix rest)
    (⌜decodeItemByteFoldFacts args n 0 payloadStart lengthBytes⌝ ∗
     ⌜decodeItemDomainAt (decodeItemReturnAddress args) decodeItemC1BDomain args⌝ ∗
     ⌜decodeItemSavedFrameFacts args frameBytes⌝ ∗
     ⌜decodeItemFoldProvenance args false prefix rest n payloadStart lengthBytes⌝ ∗
     decodeItemByteFoldStringHeader args n 0 payloadStart lengthBytes frameBytes loaded ∗
     decodeItemBranchContinuation args)%I.
Proof.
  unfold ZesuPureFactIntro. iIntros "(%Hfold & %Hdomain & %Hframe & %Hprovenance & Hheader & Hcont)".
  iApply (decodeItemStringInitializationHeaderIntro args prefix rest n payloadStart
    lengthBytes frameBytes loaded Hfold Hdomain Hframe Hprovenance).
  iFrame.
Qed.

Print Assumptions decodeItemStringInitializationWitness.

#[export] Instance decodeItemListInitializationWitness
    `{!islaG Sigma} `{!threadG}
    (args : DecodeItemArgs) (prefix : byte) (rest : list byte)
    (n payloadStart : Z) (lengthBytes frameBytes : list byte) (loaded : bv 64) :
  @ZesuPureFactIntro Sigma (decodeItemEntryAt800d6ac4 args prefix rest)
    (⌜decodeItemByteFoldFacts args n 0 payloadStart lengthBytes⌝ ∗
     ⌜decodeItemDomainAt (decodeItemReturnAddress args) decodeItemC1BDomain args⌝ ∗
     ⌜decodeItemSavedFrameFacts args frameBytes⌝ ∗
     ⌜decodeItemFoldProvenance args true prefix rest n payloadStart lengthBytes⌝ ∗
     decodeItemByteFoldListHeader args n 0 payloadStart lengthBytes frameBytes loaded ∗
     decodeItemBranchContinuation args)%I.
Proof.
  unfold ZesuPureFactIntro. iIntros "(%Hfold & %Hdomain & %Hframe & %Hprovenance & Hheader & Hcont)".
  iApply (decodeItemListInitializationHeaderIntro args prefix rest n payloadStart
    lengthBytes frameBytes loaded Hfold Hdomain Hframe Hprovenance).
  iFrame.
Qed.

Print Assumptions decodeItemListInitializationWitness.


#[export] Instance decodeItemStringInitializationAnchor
    `{!islaG Sigma} `{!threadG}
    (args : DecodeItemArgs) (prefix : byte) (rest : list byte)
    (n payloadStart : Z) (lengthBytes frameBytes : list byte) (loaded : bv 64) :
  @ZesuPureFactAnchor Sigma (decodeItemEntryAt800d6a24 args prefix rest)
    (decodeItemByteFoldStringHeader args n 0 payloadStart lengthBytes frameBytes loaded)
    (⌜decodeItemByteFoldFacts args n 0 payloadStart lengthBytes⌝ ∗
     ⌜decodeItemDomainAt (decodeItemReturnAddress args) decodeItemC1BDomain args⌝ ∗
     ⌜decodeItemSavedFrameFacts args frameBytes⌝ ∗
     ⌜decodeItemFoldProvenance args false prefix rest n payloadStart lengthBytes⌝ ∗
     decodeItemByteFoldStringHeader args n 0 payloadStart lengthBytes frameBytes loaded ∗
     decodeItemBranchContinuation args)%I.
Proof.
  exact (decodeItemStringInitializationWitness args prefix rest n payloadStart lengthBytes frameBytes loaded).
Qed.

Print Assumptions decodeItemStringInitializationAnchor.

#[export] Instance decodeItemListInitializationAnchor
    `{!islaG Sigma} `{!threadG}
    (args : DecodeItemArgs) (prefix : byte) (rest : list byte)
    (n payloadStart : Z) (lengthBytes frameBytes : list byte) (loaded : bv 64) :
  @ZesuPureFactAnchor Sigma (decodeItemEntryAt800d6ac4 args prefix rest)
    (decodeItemByteFoldListHeader args n 0 payloadStart lengthBytes frameBytes loaded)
    (⌜decodeItemByteFoldFacts args n 0 payloadStart lengthBytes⌝ ∗
     ⌜decodeItemDomainAt (decodeItemReturnAddress args) decodeItemC1BDomain args⌝ ∗
     ⌜decodeItemSavedFrameFacts args frameBytes⌝ ∗
     ⌜decodeItemFoldProvenance args true prefix rest n payloadStart lengthBytes⌝ ∗
     decodeItemByteFoldListHeader args n 0 payloadStart lengthBytes frameBytes loaded ∗
     decodeItemBranchContinuation args)%I.
Proof.
  exact (decodeItemListInitializationWitness args prefix rest n payloadStart lengthBytes frameBytes loaded).
Qed.

Print Assumptions decodeItemListInitializationAnchor.

