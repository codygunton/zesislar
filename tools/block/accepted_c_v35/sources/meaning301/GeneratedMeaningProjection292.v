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


Lemma generated6a78_meaning_projection292 `{!islaG Sigma} `{!threadG} args returnAddress :
 fp_machineAt6a78_ForwardA0N0 args returnAddress ⊢
 ⌜forall after,
 encodeResult (decodeItemInputPointer args) (decodeItemInputBytes args)
   (decodeItemBeforeStorage args) after
   (candidateSuccess true 1 (bv_unsigned (List.nth 0 (decodeItemInputBytes args) (BV 8 0)) - 192)) ->
 DecodeMeaningModuloKnownBugs args after⌝.
Proof.
 iIntros "Hentry".
 iDestruct (generated6a78_source_projection290 with "Hentry") as %Hfacts.
 iPureIntro.
 destruct Hfacts as [Hdomain [[rest Hhead] [Hclass Hfit]]].
 pose proof (proj2 Hdomain) as Hwellformed.
 destruct Hwellformed as [Hlength Hlayout].
 assert (Hmod : Z.of_nat (List.length (decodeItemInputBytes args)) mod 18446744073709551616 <= Z.of_nat (List.length (decodeItemInputBytes args))) by (apply Z.mod_le; lia).
 change (bv_unsigned (List.nth 0 (decodeItemInputBytes args) (BV 8 0)) - 192 < decodeItemInputLength args mod 18446744073709551616) in Hfit.
 rewrite Hlength in Hfit.
 assert (Haccepted : decodeItemAcceptedFacts args true 1 (bv_unsigned (List.nth 0 (decodeItemInputBytes args) (BV 8 0)) - 192)).
 { apply (decodeItemShortListAccepted args (List.nth 0 (decodeItemInputBytes args) (BV 8 0)) rest (proj2 Hdomain) Hhead Hclass).
   clear -Hfit Hmod.
   rewrite Z.add_1_l.
   apply Zlt_le_succ.
   exact (Z.lt_le_trans _ _ _ Hfit Hmod). }
 intros after Himage.
 eapply decodeItemShortListPostMeaning; [exact (proj2 Hdomain) | exact Haccepted | exact Himage | |].
 - apply (proj2 (Z.le_0_sub _ _)). exact (proj1 Hclass).
 - clear -Hclass.
   unfold word64Modulus.
   revert Hclass.
   generalize (bv_unsigned (List.nth 0 (decodeItemInputBytes args) (BV 8 0))).
   intros prefixValue Hclass. lia.
Qed.
