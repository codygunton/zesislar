Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.DecodeItemFrameImage.
Require Import ZesuSsz.Contracts.DecodeItemReturnFacts.
Require Import ZesuSsz.Compliance.DecodeItemSemanticIntroduction.
Require Import ZesuSsz.Contracts.DecodeItemBranchEntries.
Require Import ZesuSsz.Contracts.RlpDecodeItem.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
From Coq Require Import List ZArith Lia.
Open Scope Z_scope.

Lemma decodeItemSavedFrameWordsIntroduction `{!islaG Sigma} `{!threadG}
    returnAddress args (K : iProp Sigma) :
  decodeItemDomainAt returnAddress decodeItemC1BDomain args ->
  ((decodeItemStackPointer args + -16 + 0) ↦ₘ decodeItemSavedFramePointer args ∗
   (decodeItemStackPointer args + -16 + 8) ↦ₘ Z_to_bv 64 (decodeItemReturnAddress args) ∗ K)%I ⊢
  (∃ frameBytes : list byte,
   (decodeItemStackPointer args + -16 + 0) ↦ₘ∗ frameBytes ∗
   ⌜decodeItemSavedFrameFacts args frameBytes ∧
     decodeItemDomainAt (decodeItemReturnAddress args) decodeItemC1BDomain args⌝ ∗ K)%I.
Proof.
  intros Hdomain. iIntros "(Hlow & Hhigh & HK)".
  iEval (replace (decodeItemStackPointer args + -16 + 8)%Z
    with ((decodeItemStackPointer args + -16 + 0) + 8)%Z by lia) in "Hhigh".
  iDestruct (mem_mapsto_u64_pair_to_byte_array with "Hlow Hhigh") as "Hframe".
  iExists _. iFrame "Hframe HK". iPureIntro. split.
  - exact (decodeItemSavedFrameFacts_machine_words args (proj2 Hdomain)).
  - split; [reflexivity | exact (proj2 Hdomain)].
Qed.

Lemma decodeItemSavedFrameZeroRejected returnAddress args :
  decodeItemDomainAt returnAddress decodeItemC1BDomain args ->
  Z_to_bv 64 (decodeItemInputLength args) = 0%bv ->
  decodeItemRejectedFacts args.
Proof.
  intros Hdomain Hzero.
  pose proof (decodeItemDomainInputLengthBounds args (proj2 Hdomain)) as Hbounds.
  apply (f_equal bv_unsigned) in Hzero.
  rewrite (Z_to_bv_small 64 (decodeItemInputLength args)
    ltac:(unfold bv_modulus; cbn; lia)) in Hzero.
  change (decodeItemInputLength args = 0) in Hzero.
  pose proof (proj1 (proj2 Hdomain)) as Hlength.
  assert (Hempty : decodeItemInputBytes args = []).
  { apply length_zero_iff_nil. lia. }
  exact (decodeItemEmptyInputRejected args Hempty).
Qed.

Lemma decodeItemSavedFrameReturnIntroduction `{!islaG Sigma} `{!threadG}
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
Proof.
  intros Hdomain. unfold ZesuPureFactIntro. iIntros "(Hlow & Hhigh & Hcont & _)".
  iApply (decodeItemSavedFrameWordsIntroduction returnAddress args
    (decodeItemBranchContinuation args ∗ True)%I Hdomain).
  iFrame "Hlow Hhigh". unfold decodeItemBranchContinuation.
  rewrite (proj1 Hdomain). iFrame "Hcont".
Qed.

Lemma decodeItemSavedFrameRejectedIntroduction `{!islaG Sigma} `{!threadG}
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
Proof.
  intros Hdomain Hzero. unfold ZesuPureFactIntro.
  iIntros "Hsource".
  iDestruct (@zesu_pure_fact_intro _ _ _
    (decodeItemSavedFrameReturnIntroduction returnAddress args Hdomain) with "Hsource")
    as (frameBytes) "(Hframe & %Hfacts & Hcont & _)".
  iExists frameBytes. iFrame "Hframe Hcont". iPureIntro.
  destruct Hfacts as [Hframe Hown].
  pose proof (proj1 (proj2 (proj2 Hdomain))) as Hstorage.
  pose proof (decodeItemSavedFrameZeroRejected returnAddress args Hdomain Hzero) as Hrejected.
  tauto.
Qed.

Print Assumptions decodeItemSavedFrameWordsIntroduction.
Print Assumptions decodeItemSavedFrameZeroRejected.
Print Assumptions decodeItemSavedFrameReturnIntroduction.
Print Assumptions decodeItemSavedFrameRejectedIntroduction.
