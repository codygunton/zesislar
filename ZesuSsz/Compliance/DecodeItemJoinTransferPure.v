Require Import ZesuSsz.Automation.All.
From Coq Require Import ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Require Import ZesuSsz.Contracts.RlpDecodeItemByteFold.
Require Import ZesuSsz.Contracts.RlpDecodeItemFoldEntries.
Require Import ZesuSsz.Contracts.DecodeItemReturnFacts.
Require Import ZesuSsz.Contracts.DecodeItemBranchEntries.
Open Scope Z_scope.

Notation "'listSuccessorRaw' args n i payloadStart lengthBytes frameBytes next loaded" :=
  (reg_col (decodeItemSysRegs args) ∗
   "x10" ↦ᵣ RVal_Bits (Z_to_bv 64 (decodeItemOutputPointer args)) ∗
   "x11" ↦ᵣ RVal_Bits (Z_to_bv 64 (payloadStart + n)) ∗
   "x12" ↦ᵣ RVal_Bits (Z_to_bv 64 (decodeItemInputLength args)) ∗
   "x13" ↦ᵣ RVal_Bits (bv_or (Z_to_bv 64 (RlpDecodeItem.bigEndian (firstn (Z.to_nat i) lengthBytes)) ≪ 8)
     (bv_zero_extend 64 next)) ∗
   "x14" ↦ᵣ RVal_Bits (Z_to_bv 64 (n + 1)) ∗
   "x15" ↦ᵣ RVal_Bits ((Z_to_bv 64 (payloadStart + i) + 1)%bv) ∗
   "x16" ↦ᵣ RVal_Bits loaded ∗
   "x2" ↦ᵣ RVal_Bits (Z_to_bv 64 (decodeItemStackPointer args - RlpDecodeItem.decodeItemStackBytes)) ∗
   "x1" ↦ᵣ RVal_Bits (Z_to_bv 64 (decodeItemReturnAddress args)) ∗
   "x8" ↦ᵣ RVal_Bits (Z_to_bv 64 (decodeItemStackPointer args)) ∗
   decodeItemInputPointer args ↦ₘ∗ decodeItemInputBytes args ∗
   decodeItemOutputPointer args ↦ₘ∗ decodeItemBeforeStorage args ∗
   (decodeItemStackPointer args - RlpDecodeItem.decodeItemStackBytes) ↦ₘ∗ frameBytes ∗
   ⌜length frameBytes = 16%nat /\
     decodeItemByteFoldFacts args n i payloadStart lengthBytes⌝ ∗ True)%I (at level 10, args, n, i, payloadStart, lengthBytes, frameBytes, next, loaded at level 9).

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
