Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Evidence.RuleScratchRules.
Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith NArith.NArith Lia.
Require Import stdpp.bitvector.definitions.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Require Import ZesuSsz.Contracts.RlpDecodeItem.
Require Import ZesuSsz.Contracts.DecodeItemCompositional.
Require Import ZesuSsz.Contracts.DecodeItemSelected.
Require Import ZesuSsz.Contracts.IslarisMemory.
From iris.proofmode Require Import environments.
Require Import ZesuSsz.Contracts.DecodeItemReturnFacts.
Require Import ZesuSsz.Generated.DecodeItem.FP301.Pilot6a78Entries.
Require Import ZesuSsz.Evidence.GeneratedSourceProjection290.
Require Import ZesuSsz.Compliance.DecodeItemSailIntroduction.
Require Import ZesuSsz.Compliance.DecodeItemReturnExitResources.
Require Import ZesuSsz.Automation.EffectiveOverrides.
Require Import ZesuSsz.Contracts.RlpDecodeItemSchema.
Require Import ZesuSsz.Compliance.SailRun.
Open Scope Z_scope.


Require Import ZesuSsz.Evidence.GeneratedMeaningProjection292.
Lemma verify_generated6a78_meaning_projection292 (Sigma : gFunctors) (islaG0 : islaG Sigma) (H : threadG) args returnAddress :
 fp_machineAt6a78_ForwardA0N0 args returnAddress ⊢
 ⌜forall after,
 encodeResult (decodeItemInputPointer args) (decodeItemInputBytes args)
   (decodeItemBeforeStorage args) after
   (candidateSuccess true 1 (bv_unsigned (List.nth 0 (decodeItemInputBytes args) (BV 8 0)) - 192)) ->
 DecodeMeaningModuloKnownBugs args after⌝.
Proof. exact (@ZesuSsz.Evidence.GeneratedMeaningProjection292.generated6a78_meaning_projection292 Sigma islaG0 H args returnAddress). Qed.
