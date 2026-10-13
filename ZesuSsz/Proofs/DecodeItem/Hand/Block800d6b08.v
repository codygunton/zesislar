Require Import ZesuSsz.Automation.All.
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
Require Import ZesuSsz.Compliance.DecodeItemReturnExitResources.
Require Import ZesuSsz.Contracts.DecodeItemFrameImage.
Require Import ZesuSsz.Automation.PureFacts.

Definition DesignedEntry_800d6b08
    `{!islaG Sigma} `{!threadG} (args : DecodeItemArgs) (locals : DecodeItemReturnLocals) (inputPrefix : byte) (rest : list byte) (headerLength : Z) (payloadLength : Z) : iProp Sigma :=
  ((ZesuSsz.Contracts.RlpDecodeItemBlockEntries.decodeItemEntryAt800d6b08 (args) (locals) (inputPrefix) (rest) (headerLength) (payloadLength)) ∗
   True)%I.
Global Instance : LithiumUnfold (@DesignedEntry_800d6b08) := I.
Global Typeclasses Opaque DesignedEntry_800d6b08.

Lemma DesignedBoundary_800d6b08 `{!islaG Sigma} `{!threadG} (args : DecodeItemArgs) (locals : DecodeItemReturnLocals) (inputPrefix : byte) (rest : list byte) (headerLength : Z) (payloadLength : Z)  :
  decodeItemSelectedCode -∗
  instr_body 0x800d6b08
    (DesignedEntry_800d6b08 args locals inputPrefix rest headerLength payloadLength).
Proof.
  zesu_block.
  2: apply find_mem_region_array.
  1: left; unLET; assert (Houtput24 : bv_unsigned (Z_to_bv 64 (decodeItemOutputPointer args) + 24) = decodeItemOutputPointer args + 24)
    by (clear -HarrayFact14 HarrayFact15; unfold RlpDecodeItem.word64Modulus in *; bv_solve).
  1: rewrite Houtput24; cbn [length]; rewrite length_insert !length_drop !length_app !length_take H2; cbn [N.to_nat]; lia.
  1: cbn [N.eqb Pos.eqb]; iSplitR; [iPureIntro; reflexivity | idtac].
  1: iExists 24%nat; iSplitR; [iPureIntro; clear -HarrayFact14 HarrayFact15; unfold RlpDecodeItem.word64Modulus in *; bv_solve | idtac].
  1: iSplitR; [iPureIntro; cbn [length]; rewrite length_insert !length_drop !length_app !length_take H2; cbn; lia | idtac].
  1: iIntros "?".
  1: pose proof (decodeItemReturnRestorationFacts args (returnFrame locals) H1) as Hrestoration; unfold decodeItemReturnRestoration, decodeItemFrameAndStackRestoration in Hrestoration; destruct Hrestoration as (HreturnReady & HframeReady & HstackReady).
  1: zesu_run_until ltac:(fun _ => lazymatch goal with | |- envs_entails _ (li_tactic (normalize_instr_addr _) _) => unLET; lazymatch goal with | |- envs_entails _ (li_tactic (normalize_instr_addr (bv_unsigned (bv_or _ _))) _) => idtac end end). 1: unLET.
  Unshelve.
  3: exact 0%nat. 3: exact 8%nat. all: try solve [lazymatch goal with |- SHELVED_SIDECOND _ => unshelve_sidecond end; repeat f_equal; first [reflexivity | apply proof_irrel | apply bool_decide_true; bv_solve | cbn [N.to_nat]; lia]].
  1: rename select (n6 = _) into HreturnLoad. 1: rename select (n9 = _) into HframeLoad. 1: pose proof (decodeItemSavedReturnDecoder args (returnFrame locals) H1) as HreturnDecoder. 1: replace (decodeItemStackPointer args - RlpDecodeItem.decodeItemStackBytes + 8 - (decodeItemStackPointer args - RlpDecodeItem.decodeItemStackBytes)) with 8 in HreturnDecoder by lia. 1: pose proof (decodeItemSavedFramePointerDecoder args (returnFrame locals) H1) as HframeDecoder. 1: replace (decodeItemStackPointer args - RlpDecodeItem.decodeItemStackBytes + 0 - (decodeItemStackPointer args - RlpDecodeItem.decodeItemStackBytes)) with 0 in HframeDecoder by lia. 1: assert (HsavedReturn : n6 = Z_to_bv 64 (decodeItemReturnAddress args)) by (rewrite HreturnLoad; exact HreturnDecoder). 1: assert (HsavedFrame : n9 = decodeItemSavedFramePointer args) by (rewrite HframeLoad; exact HframeDecoder). 1: zesu_expose_environment_alias; rewrite HsavedReturn HsavedFrame.
  1: assert (HreturnLowBit : bv_extract 0 1 (Z_to_bv 64 (decodeItemReturnAddress args)) = BV 1 0) by (clear -HarrayFact23 HarrayFact24 HarrayFact25; unfold RlpDecodeItem.word64Modulus in *; bv_solve). 1: pose (decodeItemMaskedReturnAddress _ HreturnLowBit) as HmaskedReturn. 1: assert (HreturnAddZero : bv_add (Z_to_bv 64 (decodeItemReturnAddress args)) (BV 64 0) = Z_to_bv 64 (decodeItemReturnAddress args)) by bv_solve. 1: rewrite HreturnAddZero HmaskedReturn Z_to_bv_unsigned bv_wrap_small; last (unfold bv_modulus; change (0 <= decodeItemReturnAddress args < RlpDecodeItem.word64Modulus); lia). 1: notypeclasses refine (tac_li_tactic _ _ (normalize_instr_addr_hint (decodeItemReturnAddress args) (decodeItemReturnAddress args) eq_refl) _ _). 1: cbn [li_tactic_P normalize_instr_addr_hint]. 1: liFindInContext.
  1: iMatchHyp ltac:(fun name resource => lazymatch resource with | (?base ↦ₘ∗ ?values)%I => constr_eq base (decodeItemOutputPointer args); iExists values end). 1: iSplitR. 1: rename select (length (returnStorage locals) = _) into HstorageLength. 1: rename select (decodeItemLongAcceptedFacts args _ _ _) into Haccepted. 1: rename select (returnStorage locals = _) into HstorageBefore. 1: rename select (bv_unsigned (returnA1 locals) = _) into HreturnA1. 1: rename select (bv_unsigned (returnA3 locals) = _) into HreturnA3. 1: rename select (bv_unsigned (returnA4 locals) = _) into HreturnA4. 1: rename select (0 <= RlpDecodeItem.bigEndian _) into HpayloadNonnegative.
  1: iPureIntro; split; [exact H0 | idtac]. 1: lazymatch goal with |- DecodeMeaningModuloKnownBugs args ?after => assert (HcanonicalImage : after = decodeItemOkBytes (returnStorage locals) (bv_to_little_endian 8 8 (bv_unsigned (returnA1 locals))) (bv_to_little_endian 8 8 (bv_unsigned (returnA3 locals))) (bv_to_little_endian 8 8 (bv_unsigned (returnA4 locals))) true) by (generalize HstorageLength; generalize (returnStorage locals); intros before Hlength; clear -before Hlength locals; do 40 (destruct before as [|? before]; [discriminate |]); destruct before; [unfold decodeItemOkBytes, bv_to_little_endian, Z_to_little_endian; cbn [Z.iter Pos.iter Z.of_N N.to_nat take drop firstn skipn list_fmap fmap insert]; repeat (rewrite Z.land_ones; last lia); repeat (rewrite Z.shiftr_div_pow2; last lia); reflexivity | cbn in Hlength; lia]) end.
  1: rewrite HcanonicalImage. 1: eapply (decodeItemLongListPostMeaning args _ (1 + (bv_unsigned inputPrefix - 247)) (RlpDecodeItem.bigEndian (take (Z.to_nat (bv_unsigned inputPrefix - 247)) rest))). 1: exact (proj2 H0). 1: exact Haccepted. 1: rewrite <- HstorageBefore; apply decodeItemOkBytes_encodeSuccess. 1: exact HstorageLength. 1-3: apply length_bv_to_little_endian; compute; discriminate. 1: rewrite (littleEndian_machine_bytes 8); last (change (0 <= bv_unsigned (returnA1 locals) < bv_modulus 64); apply bv_unsigned_in_range). 1: rewrite HreturnA1; unfold RlpDecodeItemSchema.itemPayloadPointer; rewrite H3; cbn; assert (Hpneq : (bv_unsigned inputPrefix =? 128) = false) by (apply Z.eqb_neq; lia); rewrite Hpneq; reflexivity. 1: rewrite (littleEndian_machine_bytes 8); [exact HreturnA3 | change (0 <= bv_unsigned (returnA3 locals) < bv_modulus 64); apply bv_unsigned_in_range]. 1: rewrite (littleEndian_machine_bytes 8); [exact HreturnA4 | change (0 <= bv_unsigned (returnA4 locals) < bv_modulus 64); apply bv_unsigned_in_range]. 1: lia. 1: exact HpayloadNonnegative.
  1: pose proof (decodeItemStackEpilogueRestored args) as HstackRestored. 1: rename select (length (returnFrame locals) = _) into HframeLength. 1: unfold decodeItemExitResources; rewrite HstackRestored; iFrame. 1: iRename select ((decodeItemStackPointer args - RlpDecodeItem.decodeItemStackBytes) ↦ₘ∗ _)%I into "HframeBytes". 1: iDestruct (IslarisMemory.mem_mapsto_byte_array_to_mapsto_len 16 with "HframeBytes") as "Hframe"; first exact HframeLength. 1: iSplitL "Hframe"; last done. 1: iApply (ghost_state.mem_mapsto_mapsto_to_uninit with "Hframe").
  1: pose proof (decodeItemSavedReturnDecoder args (returnFrame locals) H1) as HreturnDecoder. 1: replace (decodeItemStackPointer args - RlpDecodeItem.decodeItemStackBytes + 8 - (decodeItemStackPointer args - RlpDecodeItem.decodeItemStackBytes)) with 8 in HreturnDecoder by lia. 1: assert (HreturnSecondBit : bv_extract 0 1 (bv_shiftr (bv_or (bv_and (bv_add (Z_to_bv 64 (decodeItemReturnAddress args)) (BV 64 0)) (BV 64 18446744073709551614)) (BV 64 0)) (BV 64 1)) = BV 1 0) by (clear -HarrayFact23 HarrayFact24 HarrayFact25; unfold RlpDecodeItem.word64Modulus in *; bv_simplify_arith; assert (Hlow : bv_extract 0 1 (Z_to_bv 64 (decodeItemReturnAddress args)) = BV 1 0) by bv_solve; pose proof (decodeItemMaskedReturnAddress (Z_to_bv 64 (decodeItemReturnAddress args)) Hlow) as Hmask; bv_simplify_arith Hmask; rewrite Z.add_0_r Hmask (bv_wrap_small 64 (decodeItemReturnAddress args)); last (change (0 <= decodeItemReturnAddress args < 2^64); lia); change ((decodeItemReturnAddress args / 2) mod 2 = 0); assert (Hmultiple : decodeItemReturnAddress args = (decodeItemReturnAddress args / 4 * 2) * 2) by (pose proof (Z.div_mod (decodeItemReturnAddress args) 4 ltac:(lia)); lia); rewrite Hmultiple Z.div_mul; last lia; apply Z.mod_mul; lia). 1: unLET; rename select (n6 = _) into HreturnLoad; rewrite HreturnLoad HreturnDecoder HreturnSecondBit in H70; discriminate.
Qed.
