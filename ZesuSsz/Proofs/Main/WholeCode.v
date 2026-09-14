Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.Endpoints.
Require Import ZesuSsz.Contracts.DecodeHeap.
Require Import ZesuSsz.Proofs.Main.PrefixToDecodeEntry.
Require Import ZesuSsz.Proofs.Main.SuccessOutcome.
Require Import ZesuSsz.Proofs.Main.FailureAfterConcreteDecode.
Require Import ZesuSsz.Proofs.Main.SuccessResources.
Require Import ZesuSsz.Proofs.Main.SuccessFinish.
Require Import ZesuSsz.Proofs.Main.FailureAfterDecode.
Require Import ZesuSsz.Proofs.Main.DecodeTail.
Require Import ZesuSsz.Proofs.Main.Dispatch.
Require Import ZesuSsz.Proofs.Main.OutcomeCalls.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessNativeContract.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessObservation.
Require Import ZesuSsz.Proofs.WriteFailure.WriteFailure.
Require Import ZesuSsz.Proofs.ZkvmExit.TraceContract.

Require Import ZesuSsz.Proofs.Main.WholeResources.

Local Opaque writeSuccessNativeCode.

Lemma main_success_outcome_code `{!islaG Sigma} `{!threadG}
 (allows : DecodeBoundaryArgs -> DecodeBoundaryOutcome WriteSuccessObservation -> Prop)
 (outputRelation : WriteSuccessOutputRelation WriteSuccessObservation)
 (tail : spec) (args : DecodeBoundaryArgs) (observation : WriteSuccessObservation) :
 mainSuccessOutcomeCode tail ⊣⊢
 islarisCode _ _ (mainSuccessOutcomeResources allows outputRelation tail args observation).
Proof.
 rewrite /mainSuccessOutcomeCode /mainSuccessOutcomeResources
  /mainSuccessAfterDecodeResources /mainSuccessFinishResources /=.
 iSplit.
 - iIntros "(Hdispatch&Hcall&Hwriter&Hfinish&Hexit)". iFrame.
 - iIntros "((Hdispatch&Hcall)&Hwriter&(Hfinish&Hexit))". iFrame.
Qed.
Print Assumptions main_success_outcome_code.
Lemma main_failure_after_decode_code_independent `{!islaG Sigma} `{!threadG}
 (tail : spec) (sp ra : bv 64) (status : bv 16) (P : iProp Sigma) :
 islarisCode _ _ (mainFailureAfterDecodeResources tail sp ra status P) ⊣⊢
 islarisCode _ _ (mainFailureAfterDecodeResources tail (BV 64 0) (BV 64 0x14cfc) (BV 16 1) True%I).
Proof. done. Qed.
Print Assumptions main_failure_after_decode_code_independent.
