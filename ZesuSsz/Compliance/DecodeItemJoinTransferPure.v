Require Import ZesuSsz.Automation.All.
From Coq Require Import ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Require Import ZesuSsz.Contracts.RlpDecodeItemByteFold.
Require Import ZesuSsz.Contracts.RlpDecodeItemFoldEntries.
Require Import ZesuSsz.Contracts.DecodeItemReturnFacts.
Require Import ZesuSsz.Contracts.DecodeItemBranchEntries.
Open Scope Z_scope.

(* These lemmas package unchanged resources for the two fold joins.
   The corresponding instruction steps remain machine obligations. *)
Lemma decodeItemStringHeaderIntro `{!islaG Sigma} `{!threadG}
    (args : DecodeItemArgs) (prefix : byte) (rest : list byte) (n i payloadStart : Z)
    (lengthBytes frameBytes : list byte) (loaded : bv 64) :
  i < n ->
  decodeItemDomainAt (decodeItemReturnAddress args) decodeItemC1BDomain args ->
  decodeItemSavedFrameFacts args frameBytes ->
  decodeItemFoldProvenance args false prefix rest n payloadStart lengthBytes ->
  ⊢ (decodeItemByteFoldStringHeader args n i payloadStart lengthBytes frameBytes loaded ∗
   decodeItemBranchContinuation args -∗ decodeItemEntryAt800d6a24 args prefix rest)%I.
Proof.
  intros Hguard Hdomain Hframe Hprovenance. iIntros "[Hfold Hcont]".
  iExists n, i, payloadStart, lengthBytes, frameBytes, loaded.
  iFrame.
  iPureIntro; split; [exact Hguard | split; [exact Hdomain | split; assumption]].
Qed.

Lemma decodeItemListHeaderIntro `{!islaG Sigma} `{!threadG}
    (args : DecodeItemArgs) (prefix : byte) (rest : list byte) (n i payloadStart : Z)
    (lengthBytes frameBytes : list byte) (loaded : bv 64) :
  i < n ->
  decodeItemDomainAt (decodeItemReturnAddress args) decodeItemC1BDomain args ->
  decodeItemSavedFrameFacts args frameBytes ->
  decodeItemFoldProvenance args true prefix rest n payloadStart lengthBytes ->
  ⊢ (decodeItemByteFoldListHeader args n i payloadStart lengthBytes frameBytes loaded ∗
   decodeItemBranchContinuation args -∗ decodeItemEntryAt800d6ac4 args prefix rest)%I.
Proof.
  intros Hguard Hdomain Hframe Hprovenance. iIntros "[Hfold Hcont]".
  iExists n, i, payloadStart, lengthBytes, frameBytes, loaded.
  iSplit; first (iPureIntro; split; [exact Hguard | split; [exact Hdomain | split; assumption]]).
  iFrame.
Qed.

Print Assumptions decodeItemStringHeaderIntro.
Print Assumptions decodeItemListHeaderIntro.
