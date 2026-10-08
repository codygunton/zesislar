Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Compliance.DecodeItemHints.
Require Import ZesuSsz.Contracts.DecodeItemFrameImage.
Require Import ZesuSsz.Contracts.DecodeItemReturnFacts.
Require Import ZesuSsz.Compliance.DecodeItemSemanticIntroduction.
Require Import ZesuSsz.Contracts.DecodeItemBranchEntries.
Require Import ZesuSsz.Contracts.RlpDecodeItem.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
From Coq Require Import List ZArith Lia.
Open Scope Z_scope.


Lemma savedFrameRootGoal9 `{!islaG Sigma} `{!threadG}
    returnAddress args :
  decodeItemDomainAt returnAddress decodeItemC1BDomain args ->
  ZesuPureFactIntro
    (∃ frameBytes : list byte,
      (decodeItemStackPointer args + -16 + 0) ↦ₘ∗ frameBytes ∗
      ⌜decodeItemSavedFrameFacts args frameBytes ∧
        decodeItemDomainAt (decodeItemReturnAddress args) decodeItemC1BDomain args⌝ ∗
      decodeItemBranchContinuation args ∗ True)%I
    ((decodeItemStackPointer args + -16 + 0) ↦ₘ decodeItemSavedFramePointer args ∗
      (decodeItemStackPointer args + -16 + 8) ↦ₘ Z_to_bv 64 (decodeItemReturnAddress args) ∗
      decodeItemBranchContinuationAt args returnAddress ∗ True)%I.
Proof. intros Hdomain. typeclasses eauto. Qed.

Lemma savedFrameRootGoal8 `{!islaG Sigma} `{!threadG}
    returnAddress args :
  decodeItemDomainAt returnAddress decodeItemC1BDomain args ->
  Z_to_bv 64 (decodeItemInputLength args) = 0%bv ->
  ZesuPureFactIntro
    (∃ frameBytes : list byte,
      ((decodeItemStackPointer args + -16 + 0) ↦ₘ∗ frameBytes ∗
       (⌜decodeItemDomainAt (decodeItemReturnAddress args) decodeItemC1BDomain args ∧
         decodeItemSavedFrameFacts args frameBytes ∧ length (decodeItemBeforeStorage args) = 40%nat⌝ ∗
        decodeItemBranchContinuation args ∗ True)) ∗
      ⌜decodeItemRejectedFacts args ∧ decodeItemBeforeStorage args = decodeItemBeforeStorage args⌝)%I
    ((decodeItemStackPointer args + -16 + 0) ↦ₘ decodeItemSavedFramePointer args ∗
      (decodeItemStackPointer args + -16 + 8) ↦ₘ Z_to_bv 64 (decodeItemReturnAddress args) ∗
      decodeItemBranchContinuationAt args returnAddress ∗ True)%I.
Proof. intros Hdomain Hzero. typeclasses eauto. Qed.

Lemma savedFrameMissingDomain `{!islaG Sigma} `{!threadG} (returnAddress : Z) (args : DecodeItemArgs) :
  True.
Proof.
  let target := constr:(ZesuPureFactIntro
    (∃ frameBytes : list byte,
      (decodeItemStackPointer args + -16 + 0) ↦ₘ∗ frameBytes ∗
      ⌜decodeItemSavedFrameFacts args frameBytes ∧
        decodeItemDomainAt (decodeItemReturnAddress args) decodeItemC1BDomain args⌝ ∗
      decodeItemBranchContinuation args ∗ True)%I
    ((decodeItemStackPointer args + -16 + 0) ↦ₘ decodeItemSavedFramePointer args ∗
      (decodeItemStackPointer args + -16 + 8) ↦ₘ Z_to_bv 64 (decodeItemReturnAddress args) ∗
      decodeItemBranchContinuationAt args returnAddress ∗ True)%I) in
  assert_fails (assert target by typeclasses eauto).
  exact I.
Qed.

Lemma savedFrameMissingZero `{!islaG Sigma} `{!threadG} (returnAddress : Z) (args : DecodeItemArgs) :
  decodeItemDomainAt returnAddress decodeItemC1BDomain args -> True.
Proof. intros Hdomain.
  let target := constr:(ZesuPureFactIntro
    (∃ frameBytes : list byte,
      ((decodeItemStackPointer args + -16 + 0) ↦ₘ∗ frameBytes ∗
       (⌜decodeItemDomainAt (decodeItemReturnAddress args) decodeItemC1BDomain args ∧
         decodeItemSavedFrameFacts args frameBytes ∧ length (decodeItemBeforeStorage args) = 40%nat⌝ ∗
        decodeItemBranchContinuation args ∗ True)) ∗
      ⌜decodeItemRejectedFacts args ∧ decodeItemBeforeStorage args = decodeItemBeforeStorage args⌝)%I
    ((decodeItemStackPointer args + -16 + 0) ↦ₘ decodeItemSavedFramePointer args ∗
      (decodeItemStackPointer args + -16 + 8) ↦ₘ Z_to_bv 64 (decodeItemReturnAddress args) ∗
      decodeItemBranchContinuationAt args returnAddress ∗ True)%I) in
  assert_fails (assert target by typeclasses eauto).
  exact I.
Qed.

