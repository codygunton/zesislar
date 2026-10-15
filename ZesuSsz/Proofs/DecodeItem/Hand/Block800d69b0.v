Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Proofs.DecodeItem.Hand.Common.
Require Import ZesuSsz.Automation.Approved.
Require Import ZesuSsz.Compliance.DecodeItemHints.
Require Import ZesuSsz.Contracts.DecodeItemCompositional.
Require Import isla.isla.
Require Import ZesuSsz.Stock.Closure.index_decodeItem.
Require Import ZesuSsz.Contracts.DecodeItemBranchEntries.
Require Import ZesuSsz.Contracts.DecodeItemReturnFacts.
Require Import ZesuSsz.Automation.SealedCoverage.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Require Import ZesuSsz.Contracts.DecodeItemSelected.
Require Import SailStdpp.MachineWord.
Require Import ZesuSsz.Automation.ReturnWand.
Require Import ZesuSsz.Contracts.RlpDecodeItemBlockEntries.
Require Import ZesuSsz.Contracts.RlpDecodeItemReturnImageDef.
Require Import ZesuSsz.Contracts.RlpDecodeItemReturnImages.
From iris.proofmode Require Import environments.

Require Import ZesuSsz.Compliance.DecodeItemReturnRestorationFacts.
Require Import ZesuSsz.Compliance.DecodeItemMaskedReturnFacts.


Definition DesignedEntry_800d69b0
    `{!islaG Sigma} `{!threadG} (args : DecodeItemArgs) (locals : DecodeItemReturnLocals) (inputPrefix : byte) (rest : list byte) : iProp Sigma :=
  ((ZesuSsz.Contracts.RlpDecodeItemBlockEntries.decodeItemEntryAt800d69b0 (args) (locals) (inputPrefix) (rest)) ∗
   True)%I.
Global Instance : LithiumUnfold (@DesignedEntry_800d69b0) := I.
Global Typeclasses Opaque DesignedEntry_800d69b0.

Lemma DesignedBoundary_800d69b0 `{!islaG Sigma} `{!threadG} (args : DecodeItemArgs) (locals : DecodeItemReturnLocals) (inputPrefix : byte) (rest : list byte)  :
  decodeItemSelectedCode -∗
  instr_body 0x800d69b0
    (DesignedEntry_800d69b0 args locals inputPrefix rest).

Require Import ZesuSsz.Compliance.DecodeItemEmptyStringOutputMeaning.

Proof.
iStartProof.
zesu_expose_code_lists.
repeat first [progress iIntros (?) | progress iIntros "#?" | progress iIntros "?"].
zesu_reduce_introduced_code_lists.
repeat iDestruct select (_ ∗ _)%I as "[? ?]".
zesu_run_until ltac:(fun _ => lazymatch goal with |- envs_entails _ (find_in_context (FindMemMapsTo _) _) => idtac end).
zesu_expose_environment_alias.
iMatchHyp ltac:(fun name resource => lazymatch resource with | (?base ↦ₘ∗ ?values)%I => constr_eq base (decodeItemOutputPointer args); iApply find_in_context_mem_mapsto_semantic; iExists (MKArray 8%N base values); cbn [mem_mapsto_kind_prop]; iFrameHyp name; cbn [N.eqb Pos.eqb] end).
iSplitR; first (iPureIntro; reflexivity).
iExists 32%nat.
iSplitR; first (iPureIntro; unLET; zesu_integer_array_facts; unfold RlpDecodeItem.word64Modulus in *; bv_solve).
iSplitR; first (iPureIntro; cbn [N.to_nat]; match goal with HstorageLength : length (returnStorage locals) = 40%nat |- _ => rewrite HstorageLength end; lia).
iIntros "HselectedOutput".
zesu_run_until ltac:(fun _ => lazymatch goal with |- envs_entails _ (find_in_context (FindMemMapsTo _) _) => idtac end).
zesu_expose_environment_alias.
iMatchHyp ltac:(fun name resource => lazymatch resource with | (?base ↦ₘ∗ ?values)%I => constr_eq base (decodeItemOutputPointer args); iApply find_in_context_mem_mapsto_semantic; iExists (MKArray 8%N base values); cbn [mem_mapsto_kind_prop]; iFrameHyp name; cbn [N.eqb Pos.eqb] end).
iSplitR; first done.
iExists 0%nat.
iSplitR; first (iPureIntro; unLET; zesu_integer_array_facts; unfold RlpDecodeItem.word64Modulus in *; bv_solve).
iSplitR; first (iPureIntro; cbn [N.to_nat]; zesu_normalize_known_list_lengths; cbn [length]; zesu_normalize_known_list_lengths; lia).
iIntros "HselectedOutput".
zesu_run_until ltac:(fun _ => lazymatch goal with |- envs_entails _ (find_in_context (FindMemMapsTo _) _) => idtac end).
zesu_expose_environment_alias.
iMatchHyp ltac:(fun name resource => lazymatch resource with | (?base ↦ₘ∗ ?values)%I => constr_eq base (decodeItemOutputPointer args); iApply find_in_context_mem_mapsto_semantic; iExists (MKArray 8%N base values); cbn [mem_mapsto_kind_prop]; iFrameHyp name; cbn [N.eqb Pos.eqb] end).
iSplitR; first done.
iExists 8%nat.
iSplitR; first (iPureIntro; unLET; zesu_integer_array_facts; unfold RlpDecodeItem.word64Modulus in *; bv_solve).
iSplitR; first (iPureIntro; cbn [N.to_nat]; zesu_normalize_known_list_lengths; cbn [length]; zesu_normalize_known_list_lengths; lia).
iIntros "HselectedOutput".
zesu_run_until ltac:(fun _ => lazymatch goal with |- envs_entails _ (find_in_context (FindMemMapsTo _) _) => idtac end).
zesu_expose_environment_alias.
iMatchHyp ltac:(fun name resource => lazymatch resource with | (?base ↦ₘ∗ ?values)%I => constr_eq base (decodeItemOutputPointer args); iApply find_in_context_mem_mapsto_semantic; iExists (MKArray 8%N base values); cbn [mem_mapsto_kind_prop]; iFrameHyp name; cbn [N.eqb Pos.eqb] end).
iSplitR; first (iPureIntro; rewrite Z.mod_1_r; reflexivity).
iExists 16%nat.
iSplitR; first (iPureIntro; rewrite Z.div_1_r; unLET; zesu_integer_array_facts; unfold RlpDecodeItem.word64Modulus in *; bv_solve).
iSplitR; first (iPureIntro; cbn [N.to_nat]; zesu_normalize_known_list_lengths; cbn [length]; zesu_normalize_known_list_lengths; lia).
iExists eq_refl.
iIntros "HselectedOutput".
zesu_run_until ltac:(fun _ => lazymatch goal with |- envs_entails _ (find_in_context (FindMemMapsTo _) _) => idtac end).
zesu_expose_environment_alias.
iMatchHyp ltac:(fun name resource => lazymatch resource with | (?base ↦ₘ∗ ?values)%I => constr_eq base (decodeItemOutputPointer args); iApply find_in_context_mem_mapsto_semantic; iExists (MKArray 8%N base values); cbn [mem_mapsto_kind_prop]; iFrameHyp name; cbn [N.eqb Pos.eqb] end).
iSplitR; first done.
iExists 24%nat.
iSplitR; first (iPureIntro; unLET; zesu_integer_array_facts; unfold RlpDecodeItem.word64Modulus in *; bv_solve).
iSplitR; first (iPureIntro; repeat progress (rewrite ?length_insert; cbn [N.to_nat length]; zesu_normalize_known_list_lengths); lia).
iIntros "HselectedOutput".
zesu_run_until ltac:(fun _ => lazymatch goal with |- envs_entails _ (find_in_context (FindMemMapsTo _) _) => idtac end).
zesu_expose_environment_alias.
iMatchHyp ltac:(fun name resource => lazymatch resource with | (?base ↦ₘ∗ ?values)%I => unify base ((decodeItemStackPointer args - RlpDecodeItem.decodeItemStackBytes)%Z); iApply find_in_context_mem_mapsto_semantic; iExists (MKArray 8%N base values); cbn [mem_mapsto_kind_prop]; iFrameHyp name; cbn [N.eqb Pos.eqb] end).
iSplitR; first done.
iExists 8%nat.
iSplitR; first (iPureIntro; unLET; zesu_integer_array_facts; unfold RlpDecodeItem.word64Modulus, RlpDecodeItem.decodeItemStackBytes in *; bv_solve).
iSplitR; first (iPureIntro; zesu_integer_array_facts; cbn [N.to_nat]; lia).
zesu_run_until ltac:(fun _ => lazymatch goal with |- envs_entails _ (find_in_context (FindMemMapsTo _) _) => idtac end).
zesu_expose_environment_alias.
iMatchHyp ltac:(fun name resource => lazymatch resource with | (?base ↦ₘ∗ ?values)%I => unify base ((decodeItemStackPointer args - RlpDecodeItem.decodeItemStackBytes)%Z); iApply find_in_context_mem_mapsto_semantic; iExists (MKArray 8%N base values); cbn [mem_mapsto_kind_prop]; iFrameHyp name; cbn [N.eqb Pos.eqb] end).
iSplitR; first done.
iExists 0%nat.
iSplitR; first (iPureIntro; unLET; zesu_integer_array_facts; unfold RlpDecodeItem.word64Modulus, RlpDecodeItem.decodeItemStackBytes in *; bv_solve).
iSplitR; first (iPureIntro; zesu_integer_array_facts; cbn [N.to_nat]; lia).
iIntros (savedFrameWord) "%HframeRead %HframeValue HretainedFrame".
subst savedFrameWord n13.
zesu_expose_environment_alias.
unfold TRACE.
unfold LET24.
pose proof (decodeItemSavedReturnDecoder args (returnFrame locals) H1) as HreturnDecoded; repeat match type of HreturnDecoded with context[Z.to_nat (?base + ?offset - ?base)] => replace (base + offset - base)%Z with offset in HreturnDecoded by lia end; cbn [N.to_nat Z.to_nat] in HreturnDecoded; rewrite HreturnDecoded.
pose proof (decodeItemSavedFramePointerDecoder args (returnFrame locals) H1) as HframeDecoded; repeat match type of HframeDecoded with context[Z.to_nat (?base + ?offset - ?base)] => replace (base + offset - base)%Z with offset in HframeDecoded by lia end; cbn [N.to_nat Z.to_nat] in HframeDecoded; rewrite HframeDecoded.
zesu_integer_array_facts.
match goal with Hselected : ((0 <= decodeItemReturnAddress args)%Z) |- _ => rename Hselected into HreturnLower end.
match goal with Hselected : ((decodeItemReturnAddress args < RlpDecodeItem.word64Modulus)%Z) |- _ => rename Hselected into HreturnUpper end.
match goal with Hselected : ((decodeItemReturnAddress args mod 4 = 0)%Z) |- _ => rename Hselected into HreturnAligned end.
match goal with Hselected : (length (returnFrame locals) = 16%nat) |- _ => rename Hselected into HretainedFrameLength end.
hand_return_exit
 ltac:(assert (HreturnLowBit : bv_extract 0 1 (Z_to_bv 64 (decodeItemReturnAddress args)) = BV 1 0) by (clear -HreturnLower HreturnUpper HreturnAligned; unfold RlpDecodeItem.word64Modulus in *; bv_solve);
pose proof (decodeItemMaskedReturnAddress _ HreturnLowBit) as HmaskedReturn)
 ltac:(repeat lazymatch goal with
| |- envs_entails _ (normalize_instr_addr _ _) => fail 0
| |- envs_entails _ (find_in_context (FindInstrKind ?address _) _) => lazymatch address with Zpos _ => zesu_liAStep | Z0 => zesu_liAStep | Zneg _ => zesu_liAStep | _ => fail 0 end
| _ => zesu_liAStep
end)
 ltac:(rewrite Z_to_bv_unsigned (bv_wrap_small 64 (decodeItemReturnAddress args)); last (unfold bv_modulus, RlpDecodeItem.word64Modulus in *; lia);
liFindInContext)
 ltac:(iMatchHyp ltac:(fun H body => lazymatch body with | (decodeItemOutputPointer args ↦ₘ∗ ?image)%I => iExists image end))
 ltac:(idtac)
 ltac:(zesu_expose_environment_alias; unLET; rewrite (decodeItemStackEpilogueRestored args); hand_return_exit_resources ltac:(unfold decodeItemExitResourcesRegisters, decodeItemReturnedCallerRegisters, decodeItemExitResources; rewrite (bi.sep_comm ((decodeItemStackPointer args - RlpDecodeItem.decodeItemStackBytes) ↦ₘ? RlpDecodeItem.decodeItemStackBytes)%I True%I)) HretainedFrameLength)
 ltac:(assert (HreturnSecondBit : bv_extract 0%N 1%N (bv_shiftr (bv_or (bv_and (bv_add (Z_to_bv 64%N (decodeItemReturnAddress args)) (BV 64%N 0%Z)) (BV 64%N 18446744073709551614%Z)) (BV 64%N 0%Z)) (BV 64%N 1%Z)) = BV 1%N 0%Z) by (clear -HreturnLower HreturnUpper HreturnAligned; unfold RlpDecodeItem.word64Modulus in *; bv_simplify_arith; assert (Hlow : bv_extract 0%N 1%N (Z_to_bv 64%N (decodeItemReturnAddress args)) = BV 1%N 0%Z) by bv_solve; pose proof (decodeItemMaskedReturnAddress (Z_to_bv 64%N (decodeItemReturnAddress args)) Hlow) as Hmask; bv_simplify_arith Hmask; rewrite Z.add_0_r Hmask (bv_wrap_small 64%N (decodeItemReturnAddress args)); last (change (0 <= decodeItemReturnAddress args < 2^64)%Z; lia); change ((decodeItemReturnAddress args / 2) mod 2 = 0)%Z; assert (Hmultiple : (decodeItemReturnAddress args = (decodeItemReturnAddress args / 4 * 2) * 2)%Z) by (pose proof (Z.div_mod (decodeItemReturnAddress args) 4%Z ltac:(lia)); lia); rewrite Hmultiple Z.div_mul; last lia; apply Z.mod_mul; lia);
unLET; rename select (bv_extract 0 1 (_ ≫ 1) = 1%bv) into HreturnFault; rewrite HreturnSecondBit in HreturnFault; discriminate).
1: iPureIntro; split; first exact H0; change (DecodeMeaningModuloKnownBugs args (decodeItemEmptyStringUpdatedImage locals)); assert (HoutputFacts : decodeItemEmptyStringOutputFacts args locals inputPrefix rest) by (unfold decodeItemEmptyStringOutputFacts; repeat first [assumption | split]); ZesuSsz.Automation.PureFacts.zesu_saturate_derived_facts; assumption.
Unshelve.
all: zesu_finish.
Qed.
