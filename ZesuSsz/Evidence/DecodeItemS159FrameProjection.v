Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.Approved.
Require Import ZesuSsz.Compliance.DecodeItemHints.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Require Import ZesuSsz.Contracts.DecodeItemBranchEntries.
Require Import ZesuSsz.Contracts.DecodeItemReturnFacts.
From Coq Require Import ZArith NArith Lia List.
Open Scope Z_scope.


Lemma s159_frame_rejection_projection `{!islaG Sigma} `{!threadG} (args : DecodeItemArgs) :
 (∃ frameBytes : list byte,
   (((decodeItemStackPointer args + -16 + 0)%Z ↦ₘ∗ frameBytes ∗
       (⌜decodeItemDomainAt (decodeItemReturnAddress args) decodeItemC1BDomain args /\
         decodeItemSavedFrameFacts args frameBytes /\ length (decodeItemBeforeStorage args) = 40%nat⌝ ∗
        decodeItemBranchContinuation args ∗ True)) ∗
    ⌜decodeItemRejectedFacts args /\ decodeItemBeforeStorage args = decodeItemBeforeStorage args⌝))%I ⊢
 (∃ frameBytes : list byte,
  (decodeItemStackPointer args + -16 + 0)%Z ↦ₘ∗ frameBytes ∗
  ⌜decodeItemSavedFrameFacts args frameBytes /\
    decodeItemDomainAt (decodeItemReturnAddress args) decodeItemC1BDomain args⌝ ∗
  decodeItemBranchContinuation args ∗ True)%I.
Proof.
iIntros "Hsource".
iDestruct "Hsource" as (frameBytes) "((Hframe & %Hfacts & Hcont & _) & _)".
iExists frameBytes. iFrame. iPureIntro. tauto.
Qed.
