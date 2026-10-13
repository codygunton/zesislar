Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Proofs.DecodeItem.Hand.Common.
Require Import ZesuSsz.Automation.Approved.
Require Import ZesuSsz.Compliance.DecodeItemHints.
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
zesu_block.
2: apply find_mem_region_array.
1: left; unfold LET0; bv_simplify_arith; rewrite ?length_insert; cbn [length]; zesu_normalize_known_list_lengths.
1: rewrite !length_insert; zesu_normalize_known_list_lengths; cbn [N.to_nat]; rewrite bv_wrap_small; [lia | unfold bv_modulus, RlpDecodeItem.word64Modulus in *; cbn; lia].
cbn; iSplitR; [iPureIntro; reflexivity|].
iExists 24%nat.
iSplitR; [iPureIntro; bv_solve|].
iSplitR; [iPureIntro; cbn [length]; rewrite ?length_insert; zesu_normalize_known_list_lengths; cbn [N.to_nat]; lia|].
iIntros "?".
zesu_block.
iDestruct select (∃ vact : valu, ⌜vact = RVal_Bool false⌝ ∗ "rv_enable_pmp" ↦ᵣ vact)%I as (pmpValue) "[%Hpmp ?]".
subst pmpValue.
zesu_block.
repeat (iDestruct select (∃ vact : valu, ⌜vact = _⌝ ∗ _)%I as (registerValue) "[%HregisterValue ?]"; subst registerValue).
zesu_block.
notypeclasses refine (tac_li_tactic _ _ (regcol_compute_hint_hint (false, ExactShape (RVal_Bits (Z_to_bv 64 9223372036854780160))) (regcol_lookup_field "misa" "bits") [(KindReg "misa", ExactShape (RegVal_Struct [("bits", RVal_Bits (Z_to_bv 64 9223372036854780160))]))] eq_refl) _ _).
cbn [regcol_compute_hint_hint li_tactic_P].
iSplitR; [iPureIntro; do 2 f_equal; apply (proj2 (bvn_eq _ _)); split; vm_compute; reflexivity |].
iIntros "HmisaReloadCol".
zesu_block.
notypeclasses refine (tac_li_tactic _ _ (regcol_compute_hint_hint (false, ExactShape (RVal_Bits (Z_to_bv 64 0))) (regcol_lookup_field "mtvec" "bits") [(KindReg "mtvec", ExactShape (RegVal_Struct [("bits", RVal_Bits (Z_to_bv 64 0))]))] eq_refl) _ _).
cbn [regcol_compute_hint_hint li_tactic_P].
iSplitR; [iPureIntro; do 2 f_equal; apply (proj2 (bvn_eq _ _)); split; vm_compute; reflexivity |].
iIntros "HmtvecReloadCol".
zesu_block.
1: exact 8%nat.
1: prepare_sidecond; cbn; lia.
1: prepare_sidecond; cbn; match goal with HframeLength : length (returnFrame locals) = 16%nat |- _ => rewrite HframeLength end; lia.
notypeclasses refine (tac_li_tactic _ _ (regcol_compute_hint_hint (false, ExactShape (RVal_Bits (Z_to_bv 64 9223372036854780160))) (regcol_lookup_field "misa" "bits") [(KindReg "misa", ExactShape (RegVal_Struct [("bits", RVal_Bits (Z_to_bv 64 9223372036854780160))]))] eq_refl) _ _).
cbn [regcol_compute_hint_hint li_tactic_P].
iSplitR; [iPureIntro; do 2 f_equal; apply (proj2 (bvn_eq _ _)); split; vm_compute; reflexivity |].
iIntros "HmisaReloadCol".
zesu_block.
notypeclasses refine (tac_li_tactic _ _ (regcol_compute_hint_hint (false, ExactShape (RVal_Bits (Z_to_bv 64 0))) (regcol_lookup_field "mtvec" "bits") [(KindReg "mtvec", ExactShape (RegVal_Struct [("bits", RVal_Bits (Z_to_bv 64 0))]))] eq_refl) _ _).
cbn [regcol_compute_hint_hint li_tactic_P].
iSplitR; [iPureIntro; do 2 f_equal; apply (proj2 (bvn_eq _ _)); split; vm_compute; reflexivity |].
iIntros "HmtvecReloadCol".
zesu_block.
1: exact 0%nat.
1: prepare_sidecond; cbn; lia.
1: prepare_sidecond; cbn; match goal with HframeLength : length (returnFrame locals) = 16%nat |- _ => rewrite HframeLength end; lia.
notypeclasses refine (tac_li_tactic _ _ (regcol_compute_hint_hint (false, ExactShape (RVal_Bits (Z_to_bv 64 9223372036854780160))) (regcol_lookup_field "misa" "bits") [(KindReg "misa", ExactShape (RegVal_Struct [("bits", RVal_Bits (Z_to_bv 64 9223372036854780160))]))] eq_refl) _ _).
cbn [regcol_compute_hint_hint li_tactic_P].
iSplitR; [iPureIntro; do 2 f_equal; apply (proj2 (bvn_eq _ _)); split; vm_compute; reflexivity |].
iIntros "HframeMisaCol".
zesu_block.
notypeclasses refine (tac_li_tactic _ _ (regcol_compute_hint_hint (false, ExactShape (RVal_Bits (Z_to_bv 64 0))) (regcol_lookup_field "mtvec" "bits") [(KindReg "mtvec", ExactShape (RegVal_Struct [("bits", RVal_Bits (Z_to_bv 64 0))]))] eq_refl) _ _).
cbn [regcol_compute_hint_hint li_tactic_P].
iSplitR; [iPureIntro; do 2 f_equal; apply (proj2 (bvn_eq _ _)); split; vm_compute; reflexivity |].
iIntros "HframeMtvecCol".
rename select (decodeItemSavedFrameFacts args (returnFrame locals)) into HsavedFrameFacts.
hand_decode_saved_registers
 (decodeItemSavedReturnDecoder args (returnFrame locals) HsavedFrameFacts)
 (decodeItemSavedFramePointerDecoder args (returnFrame locals) HsavedFrameFacts)
 (decodeItemStackEpilogueRestored args) n7.
hand_return_exit
 ltac:(assert (HreturnLowBit : bv_extract 0 1 (Z_to_bv 64 (decodeItemReturnAddress args)) = BV 1 0) by (clear -HarrayFact23 HarrayFact24 HarrayFact25; unfold RlpDecodeItem.word64Modulus in *; bv_solve);
pose proof (decodeItemMaskedReturnAddress _ HreturnLowBit) as HmaskedReturn)
 ltac:(repeat lazymatch goal with
| |- envs_entails _ (normalize_instr_addr _ _) => fail 0
| |- envs_entails _ (find_in_context (FindInstrKind _ _) _) => fail 0
| _ => zesu_liAStep
end)
 ltac:(rewrite Z_to_bv_unsigned (bv_wrap_small 64 (decodeItemReturnAddress args)); last (unfold bv_modulus, RlpDecodeItem.word64Modulus in *; lia);
liFindInContext)
 ltac:(iMatchHyp ltac:(fun H body => lazymatch body with | (decodeItemOutputPointer args ↦ₘ∗ ?image)%I => iExists image end))
 ltac:(idtac)
 ltac:(hand_return_exit_resources ltac:(unfold decodeItemExitResources) HarrayFact3)
 ltac:(assert (HreturnSecondBit : bv_extract 0%N 1%N (bv_shiftr (bv_or (bv_and (bv_add (Z_to_bv 64%N (decodeItemReturnAddress args)) (BV 64%N 0%Z)) (BV 64%N 18446744073709551614%Z)) (BV 64%N 0%Z)) (BV 64%N 1%Z)) = BV 1%N 0%Z) by (clear -HarrayFact23 HarrayFact24 HarrayFact25; unfold RlpDecodeItem.word64Modulus in *; bv_simplify_arith; assert (Hlow : bv_extract 0%N 1%N (Z_to_bv 64%N (decodeItemReturnAddress args)) = BV 1%N 0%Z) by bv_solve; pose proof (decodeItemMaskedReturnAddress (Z_to_bv 64%N (decodeItemReturnAddress args)) Hlow) as Hmask; bv_simplify_arith Hmask; rewrite Z.add_0_r Hmask (bv_wrap_small 64%N (decodeItemReturnAddress args)); last (change (0 <= decodeItemReturnAddress args < 2^64)%Z; lia); change ((decodeItemReturnAddress args / 2) mod 2 = 0)%Z; assert (Hmultiple : (decodeItemReturnAddress args = (decodeItemReturnAddress args / 4 * 2) * 2)%Z) by (pose proof (Z.div_mod (decodeItemReturnAddress args) 4%Z ltac:(lia)); lia); rewrite Hmultiple Z.div_mul; last lia; apply Z.mod_mul; lia);
unLET; rename select (bv_extract 0 1 (_ ≫ 1) = 1%bv) into HreturnFault; rewrite HreturnSecondBit in HreturnFault; discriminate).
iPureIntro; split; first (match goal with HexitDomain : decodeItemDomainAt (decodeItemReturnAddress args) decodeItemC1BDomain args |- _ => exact HexitDomain end); change (DecodeMeaningModuloKnownBugs args (decodeItemEmptyStringUpdatedImage locals)); assert (HoutputFacts : decodeItemEmptyStringOutputFacts args locals inputPrefix rest) by (unfold decodeItemEmptyStringOutputFacts; repeat first [assumption | split]); ZesuSsz.Automation.PureFacts.zesu_saturate_derived_facts; assumption.
Unshelve.
all: prepare_sidecond.
apply (proj2 (bv_eq 64 _ _)); rewrite bv_and_unsigned; change (Z.land (bv_unsigned b13) 131072 = 0)%Z; exact H1.
Qed.
