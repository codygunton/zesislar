Require Import ZesuSsz.Automation.All.
From Coq Require Import ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Require Import ZesuSsz.Contracts.RlpDecodeItemByteFold.
Require Import ZesuSsz.Contracts.RlpDecodeItemFoldEntries.
Require Import ZesuSsz.Contracts.DecodeItemBranchEntries.
Open Scope Z_scope.

(* These lemmas package unchanged resources for the two fold joins.
   The corresponding instruction steps remain machine obligations. *)
Lemma decodeItemStringHeaderIntro `{!islaG Sigma} `{!threadG}
    (args : DecodeItemArgs) (n i payloadStart : Z)
    (lengthBytes frameBytes : list byte) (loaded : bv 64) :
  i < n ->
  decodeItemDomainAt (decodeItemReturnAddress args) decodeItemC1BDomain args ->
  decodeItemSavedFrameFacts args frameBytes ->
  ⊢ (decodeItemByteFoldStringHeader args n i payloadStart lengthBytes frameBytes loaded ∗
   decodeItemBranchContinuation args -∗ decodeItemEntryAt800d6a24 args)%I.
Proof.
  intros Hguard Hdomain Hframe. iIntros "[Hfold Hcont]".
  iExists n, i, payloadStart, lengthBytes, frameBytes, loaded.
  iSplit; first (iPureIntro; split; [exact Hguard | split; assumption]).
  iFrame.
Qed.

Lemma decodeItemListHeaderIntro `{!islaG Sigma} `{!threadG}
    (args : DecodeItemArgs) (n i payloadStart : Z)
    (lengthBytes frameBytes : list byte) (loaded : bv 64) :
  i < n ->
  decodeItemDomainAt (decodeItemReturnAddress args) decodeItemC1BDomain args ->
  decodeItemSavedFrameFacts args frameBytes ->
  ⊢ (decodeItemByteFoldListHeader args n i payloadStart lengthBytes frameBytes loaded ∗
   decodeItemBranchContinuation args -∗ decodeItemEntryAt800d6ac4 args)%I.
Proof.
  intros Hguard Hdomain Hframe. iIntros "[Hfold Hcont]".
  iExists n, i, payloadStart, lengthBytes, frameBytes, loaded.
  iSplit; first (iPureIntro; split; [exact Hguard | split; assumption]).
  iFrame.
Qed.

Print Assumptions decodeItemStringHeaderIntro.
Print Assumptions decodeItemListHeaderIntro.
