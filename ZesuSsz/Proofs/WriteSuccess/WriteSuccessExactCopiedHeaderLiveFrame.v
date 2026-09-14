Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Proofs.WriteSuccess.Interfaces.
Require Import ZesuMachineMap.Machine.
Require Import ZesuSsz.Contracts.IslarisMemory.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessNativeContract.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactCopiedValueLiveEntry.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactHeaderValue.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactTransactionsLiveSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactTransactionsSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactValueSpec.

Definition writeSuccessExactCopiedHeaderLiveFrameRest `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (base : Z) (transactions : list writeSuccessTransaction)
    (transactionBytes object : list (bv 8)) (P : iProp Sigma) : iProp Sigma :=
  (bv_unsigned sp ↦ₘ? 8 ∗ writeSuccessExactCopiedTailWords sp object ∗ (bv_unsigned sp + 120) ↦ₘ? 160 ∗
   base ↦ₘ∗ transactionBytes ∗ writeSuccessTransactionsOwn transactions ∗
   ⌜transactionLoopSourceFacts sp base transactions [] transactions transactionBytes⌝ ∗ P)%I.
Global Instance : LithiumUnfold (@writeSuccessExactCopiedHeaderLiveFrameRest) := I.

Lemma write_success_exact_copied_header_live_frame `{!islaG Sigma} `{!threadG}
    sp base transactions transactionBytes sourceBytes object (P : iProp Sigma) :
  writeSuccessExactHeaderValueFrame
    (writeSuccessExactCopiedHeaderLiveFrameRest sp base transactions transactionBytes object P)
    sp sourceBytes -∗
  writeSuccessExactCopiedValueLiveFrame sp base transactions transactionBytes sourceBytes object
    (writeSuccessNativeStaticResources ∗ P).
Proof.
  rewrite /writeSuccessExactHeaderValueFrame /writeSuccessExactCopiedHeaderLiveFrameRest
    /writeSuccessExactCopiedValueLiveFrame.
  iIntros "(Hsource & Hhigh & Hstatic & Hlow & Hwords & Hmiddle & Hbytes & Hown & Hfacts & HP)".
  iFrame.
Qed.
Print Assumptions write_success_exact_copied_header_live_frame.

