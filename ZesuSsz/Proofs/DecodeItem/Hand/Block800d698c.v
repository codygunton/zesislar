Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Proofs.DecodeItem.Hand.Common.
Require Import ZesuSsz.Automation.Approved.
Require Import ZesuSsz.Compliance.DecodeItemHints.
Require Import ZesuSsz.Contracts.DecodeItemCompositional.
Require Import ZesuSsz.Compliance.DecodeItemReturnExitResources.
Require Import ZesuSsz.Automation.PureFacts.
Require Import ZesuSsz.Compliance.DecodeItemReturnRestorationFacts.
Require Import ZesuSsz.Compliance.DecodeItemMaskedReturnFacts.
Require Import isla.isla.
Require Import ZesuSsz.Stock.Closure.index_decodeItem.
Require Import ZesuSsz.Contracts.RlpDecodeItemBlockEntries.
Require Import ZesuSsz.Contracts.DecodeItemReturnFacts.
Require Import ZesuSsz.Contracts.RlpDecodeItemReturnImageDef.
Require Import ZesuSsz.Contracts.RlpDecodeItemReturnImages.
Require Import ZesuSsz.Automation.SealedCoverage.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Require Import ZesuSsz.Contracts.DecodeItemSelected.
Require Import SailStdpp.MachineWord.
Require Import ZesuSsz.Automation.ReturnWand.
Require Import ZesuSsz.Contracts.DecodeItemBranchEntries.
From iris.proofmode Require Import environments.

Definition DesignedEntry_800d698c
    `{!islaG Sigma} `{!threadG} (args : DecodeItemArgs) (locals : DecodeItemReturnLocals) (pointerBytes : list byte) (lengthBytes : list byte) (inputPrefix : byte) (rest : list byte) (isLiteral : bool) : iProp Sigma :=
  ((ZesuSsz.Contracts.RlpDecodeItemBlockEntries.decodeItem698cCaseResources (args) (locals) (pointerBytes) (lengthBytes) (inputPrefix) (rest) (isLiteral)) ∗
   True)%I.
Global Instance : LithiumUnfold (@DesignedEntry_800d698c) := I.
Global Typeclasses Opaque DesignedEntry_800d698c.

Lemma DesignedBoundary_800d698c `{!islaG Sigma} `{!threadG} (args : DecodeItemArgs) (locals : DecodeItemReturnLocals) (pointerBytes : list byte) (lengthBytes : list byte) (inputPrefix : byte) (rest : list byte) (isLiteral : bool)  :
  decodeItemSelectedCode -∗
  instr_body 0x800d698c
    (DesignedEntry_800d698c args locals pointerBytes lengthBytes inputPrefix rest isLiteral).
Proof.
iStartProof.
zesu_expose_code_lists.
repeat first [progress iIntros (?) | progress iIntros "#?" | progress iIntros "?"].
zesu_reduce_introduced_code_lists.
repeat iDestruct select (_ ∗ _)%I as "[? ?]".
zesu_run_until ltac:(fun _ => lazymatch goal with |- envs_entails _ (find_in_context (FindMemMapsTo _) _) => idtac end).
zesu_expose_environment_alias.
iMatchHyp ltac:(fun name resource => lazymatch resource with | (?base ↦ₘ∗ ?values)%I => constr_eq base (decodeItemOutputPointer args); iApply find_in_context_mem_mapsto_semantic; iExists (MKArray 8%N base values); cbn [mem_mapsto_kind_prop]; iFrameHyp name; cbn [N.eqb Pos.eqb] end).
iSplitR; first (iPureIntro; cbn; lia).
iExists 16%nat.
iSplitR; first (iPureIntro; unLET; zesu_integer_array_facts; unfold RlpDecodeItem.word64Modulus in *; bv_solve).
iSplitR; first (iPureIntro; rewrite H2; lia).
iExists eq_refl.
zesu_expose_environment_alias.
iIntros "HselectedOutput".
zesu_run_until ltac:(fun _ => lazymatch goal with |- envs_entails _ (find_in_context (FindMemMapsTo _) _) => idtac end).
zesu_expose_environment_alias.
iMatchHyp ltac:(fun name resource => lazymatch resource with | (?base ↦ₘ∗ ?values)%I => constr_eq base (decodeItemOutputPointer args); iApply find_in_context_mem_mapsto_semantic; iExists (MKArray 8%N base values); cbn [mem_mapsto_kind_prop]; iFrameHyp name; cbn [N.eqb Pos.eqb] end).
iSplitR; first done.
iExists 24%nat.
iSplitR; first (iPureIntro; unLET; zesu_integer_array_facts; unfold RlpDecodeItem.word64Modulus in *; bv_solve).
iSplitR; first (iPureIntro; rewrite length_insert H2; cbn; lia).
zesu_expose_environment_alias.
iIntros "Hstored24".
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
pose proof (decodeItemSavedReturnDecoder args (returnFrame locals) H1) as HreturnWord.
replace (decodeItemStackPointer args - RlpDecodeItem.decodeItemStackBytes + 8 - (decodeItemStackPointer args - RlpDecodeItem.decodeItemStackBytes))%Z with 8%Z in HreturnWord by lia.
change (Z_to_bv 64%N (little_endian_to_bv 8%N (take 8%nat (drop 8%nat (returnFrame locals)))) = Z_to_bv 64%N (decodeItemReturnAddress args)) in HreturnWord.
zesu_integer_array_facts.
assert (HreturnAligned : bv_extract 0%N 1%N (Z_to_bv 64%N (decodeItemReturnAddress args)) = BV 1%N 0%Z) by bv_solve.
zesu_expose_environment_alias.
unLET.
rewrite HreturnWord.
zesu_run_until ltac:(fun _ => lazymatch goal with |- iris.proofmode.environments.envs_entails _ (li_tactic (normalize_instr_addr ?a) _) => let address := eval cbv in a in tryif is_closed_term address then fail else idtac end).
1: unLET.
1: assert (HreturnAddZero : bv_add (Z_to_bv 64%N (decodeItemReturnAddress args)) (BV 64%N 0%Z) = Z_to_bv 64%N (decodeItemReturnAddress args)) by bv_solve.
1: (rewrite HreturnAddZero (decodeItemMaskedReturnAddress _ HreturnAligned) Z_to_bv_unsigned bv_wrap_small; last (unfold bv_modulus; change (0 <= decodeItemReturnAddress args < RlpDecodeItem.word64Modulus)%Z; lia)).
1: notypeclasses refine (tac_li_tactic _ _ (normalize_instr_addr_hint (decodeItemReturnAddress args) (decodeItemReturnAddress args) eq_refl) _ _).
1: cbn [li_tactic_P normalize_instr_addr_hint].
1: liFindInContext.
1: assert (HframeWord : Z_to_bv 64%N (little_endian_to_bv 8%N (take 8%nat (drop 0%nat (returnFrame locals)))) = decodeItemSavedFramePointer args) by (pose proof (decodeItemSavedFramePointerDecoder args (returnFrame locals) H1) as Hdecoder; replace (decodeItemStackPointer args - RlpDecodeItem.decodeItemStackBytes + 0 - (decodeItemStackPointer args - RlpDecodeItem.decodeItemStackBytes))%Z with 0%Z in Hdecoder by lia; exact Hdecoder).
1: rewrite HframeWord (decodeItemStackEpilogueRestored args).
1: zesu_expose_environment_alias.
1: iMatchHyp ltac:(fun name resource => lazymatch resource with | (?base ↦ₘ∗ ?values)%I => constr_eq base (decodeItemOutputPointer args); iExists values end).
1: iSplitR.
2: hand_return_exit_resources ltac:(unfold decodeItemExitResourcesRegisters, decodeItemReturnedCallerRegisters, decodeItemExitResources; rewrite (bi.sep_comm ((decodeItemStackPointer args - RlpDecodeItem.decodeItemStackBytes) ↦ₘ? RlpDecodeItem.decodeItemStackBytes)%I True%I)) (proj1 H1).
2: match goal with Hpin : ?T |- _ => let expected := constr:((0 <= decodeItemReturnAddress args)%Z) in unify T expected; rename Hpin into HreturnNonnegative end.
2: match goal with Hpin : ?T |- _ => let expected := constr:((decodeItemReturnAddress args < RlpDecodeItem.word64Modulus)%Z) in unify T expected; rename Hpin into HreturnUpperBound end.
2: match goal with Hpin : ?T |- _ => let expected := constr:((decodeItemReturnAddress args mod 4 = 0)%Z) in unify T expected; rename Hpin into HreturnAddressAligned end.
2: assert (HreturnSecondBit : bv_extract 0%N 1%N (bv_shiftr (bv_or (bv_and (bv_add (Z_to_bv 64%N (decodeItemReturnAddress args)) (BV 64%N 0%Z)) (BV 64%N 18446744073709551614%Z)) (BV 64%N 0%Z)) (BV 64%N 1%Z)) = BV 1%N 0%Z) by (clear -HreturnNonnegative HreturnUpperBound HreturnAddressAligned; unfold RlpDecodeItem.word64Modulus in *; bv_simplify_arith; assert (Hlow : bv_extract 0%N 1%N (Z_to_bv 64%N (decodeItemReturnAddress args)) = BV 1%N 0%Z) by bv_solve; pose proof (decodeItemMaskedReturnAddress (Z_to_bv 64%N (decodeItemReturnAddress args)) Hlow) as Hmask; bv_simplify_arith Hmask; rewrite Z.add_0_r Hmask (bv_wrap_small 64%N (decodeItemReturnAddress args)); last (change (0 <= decodeItemReturnAddress args < 2^64)%Z; lia); change ((decodeItemReturnAddress args / 2) mod 2 = 0)%Z; assert (Hmultiple : (decodeItemReturnAddress args = (decodeItemReturnAddress args / 4 * 2) * 2)%Z) by (pose proof (Z.div_mod (decodeItemReturnAddress args) 4%Z ltac:(lia)); lia); rewrite Hmultiple Z.div_mul; last lia; apply Z.mod_mul; lia).
2: (unLET; match goal with Hpin : ?T |- _ => let expected := constr:(bv_extract 0%N 1%N (bv_shiftr (bv_or (bv_and (bv_add (Z_to_bv 64%N (decodeItemReturnAddress args)) (BV 64%N 0%Z)) (BV 64%N 18446744073709551614%Z)) (BV 64%N 0%Z)) (BV 64%N 1%Z)) = BV 1%N 1%Z) in unify T expected; rename Hpin into HreturnFaultBit; rewrite HreturnSecondBit in HreturnFaultBit; discriminate end).
1: (iPureIntro; split; first exact H0).
1: pose proof (ResultImage.fieldImage_slice _ _ _ H9 : take 8%nat (drop 0%nat (returnStorage locals)) = AbiBytes.word64Bytes (bv_unsigned (returnA1 locals))) as HpointerSlice.
1: pose proof (ResultImage.fieldImage_slice _ _ _ H10) as HlengthSlice; rewrite H12 in HlengthSlice.
1: pose proof (ResultImage.fieldImage_slice _ _ _ H11) as HstatusSlice; change (take 2%nat (drop 32%nat (returnStorage locals)) = [Z_to_bv 8%N 0%Z; Z_to_bv 8%N 0%Z]) in HstatusSlice.
1: pose proof (ResultImage.preservedImage_slice _ _ _ _ H13) as Hpad17Slice.
1: pose proof (ResultImage.preservedImage_slice _ _ _ _ H14) as Hpad34Slice.
1: assert (HbyteZero : (0%bv : bv 8%N) = Z_to_bv 8%N 0%Z) by (apply bv_eq; reflexivity).
1: lazymatch goal with |- DecodeMeaningModuloKnownBugs args ?after => assert (HcanonicalImage : after = decodeItemOkBytes (decodeItemBeforeStorage args) (AbiBytes.word64Bytes (bv_unsigned (returnA1 locals))) lengthBytes (bv_to_little_endian 8%Z 8%N (bv_unsigned (returnA2 locals))) false) by (unfold decodeItemOkBytes; rewrite <- HpointerSlice; rewrite <- HlengthSlice; rewrite <- HstatusSlice; rewrite <- Hpad17Slice; rewrite <- Hpad34Slice; replace (N.to_nat 8%N) with 8%nat by reflexivity; generalize H2; generalize (returnStorage locals); intros before Hlength; clear -before Hlength locals HbyteZero; do 40 (destruct before as [|? before]; [discriminate |]); destruct before; [unfold bv_to_little_endian, Z_to_little_endian; cbn [Z.iter Pos.iter Z.of_N N.to_nat take drop firstn skipn list_fmap fmap insert]; repeat (rewrite Z.land_ones; last lia); repeat (rewrite Z.shiftr_div_pow2; last lia); cbv [list_insert insert N.to_nat app take drop firstn skipn]; rewrite HbyteZero; reflexivity | cbn in Hlength; lia]) end.
1: rewrite HcanonicalImage.
1: rewrite <- (decodeItemStoredWordBytes (returnA1 locals)).
1: destruct isLiteral.
1: (eapply decodeItemLiteralPostMeaning; [exact (proj2 H0) | exact H8 | rewrite H3; apply return_800d69a0_literal; try assumption; try (apply length_bv_to_little_endian; compute; discriminate); rewrite decodeItemStoredWordValue; first [solve [rewrite H5; lia] | solve [rewrite H7; reflexivity]]]).
1: (eapply (decodeItemShortStringPostMeaning args _ (bv_unsigned inputPrefix - 128)%Z); [exact (proj2 H0) | exact H8 | rewrite H3; apply return_800d69a0_shortString; try assumption; try (apply length_bv_to_little_endian; compute; discriminate); rewrite decodeItemStoredWordValue; first [solve [rewrite H5; lia] | solve [rewrite H7; symmetry; apply Z.mod_small; unfold RlpDecodeItem.word64Modulus; lia]] | lia | unfold RlpDecodeItem.word64Modulus; lia]).
Unshelve. all: repeat progress zesu_finish.
Qed.
