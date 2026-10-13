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
iStartProof.
zesu_expose_code_lists.
repeat first [progress iIntros (?) | progress iIntros "#?" | progress iIntros "?"].
zesu_reduce_introduced_code_lists.
repeat iDestruct select (_ ∗ _)%I as "[? ?]".
1: time "output-index32" (zesu_run_until ltac:(fun _ => lazymatch goal with | |- envs_entails _ (@iris.bi.interface.bi_exist _ nat _) => idtac end)).
1: iExists 32%nat.
1: time "output-index0" (zesu_run_until ltac:(fun _ => lazymatch goal with | |- envs_entails _ (@iris.bi.interface.bi_exist _ nat _) => idtac end)).
1: iExists 0%nat.
1: time "output-index8" (zesu_run_until ltac:(fun _ => lazymatch goal with | |- envs_entails _ (@iris.bi.interface.bi_exist _ nat _) => idtac end)).
1: iExists 8%nat.
1: time "output-index16" (zesu_run_until ltac:(fun _ => lazymatch goal with | |- envs_entails _ (@iris.bi.interface.bi_exist _ nat _) => idtac end)).
1: iExists 16%nat.
1: time "output-index24-boundary" (zesu_run_until ltac:(fun _ => lazymatch goal with | |- envs_entails _ (@iris.bi.interface.bi_exist _ nat _) => idtac end)).
  1: unLET; assert (Hstore24Address : bv_unsigned (bv_add (Z_to_bv 64 (decodeItemOutputPointer args)) (24%bv : bv 64)) = (decodeItemOutputPointer args + 24)%Z) by (clear -HarrayFact14 HarrayFact15; unfold RlpDecodeItem.word64Modulus in *; bv_solve). 1: rewrite Hstore24Address. 1: notypeclasses refine (tac_find_in_context (ZesuMemRegionSearch (decodeItemOutputPointer args + 24)) (find_mem_region_inst (decodeItemOutputPointer args + 24)) _). 1: simpl; repeat liExist false. 1: zesu_expose_environment_alias. 1: iRename select ((decodeItemOutputPointer args) ↦ₘ∗ _)%I into "HselectedOutput". 1: iMatchHyp ltac:(fun name resource => lazymatch resource with | (?base ↦ₘ∗ ?values)%I => constr_eq base (decodeItemOutputPointer args); notypeclasses refine (tac_find_hyp_equal (ZesuMemRegionSearch (decodeItemOutputPointer args + 24)) resource _ _ _ _ _) end). 1: apply find_mem_region_array.
  1: left; cbn [length]; rewrite length_insert !length_drop !length_app !length_take H2; cbn [N.to_nat]; lia. 1: iFrame "HselectedOutput". 1: cbn [N.eqb Pos.eqb]; iSplitR; [iPureIntro; reflexivity | idtac]. 1: iExists 24%nat; iSplitR; [iPureIntro; cbn; lia | idtac]. 1: iSplitR; [iPureIntro; cbn [length]; rewrite length_insert !length_drop !length_app !length_take H2; cbn; lia | idtac]. 1: iIntros "HselectedOutput".
  1: pose proof (decodeItemReturnRestorationFacts args (returnFrame locals) H1) as Hrestoration; unfold decodeItemReturnRestoration, decodeItemFrameAndStackRestoration in Hrestoration; destruct Hrestoration as (HreturnReady & HframeReady & HstackReady). 1: time "return-frame-index8" (zesu_run_until ltac:(fun _ => lazymatch goal with | |- envs_entails _ (@iris.bi.interface.bi_exist _ nat _) => idtac end)). 1: iExists 8%nat.
  1: iSplitR; [iPureIntro; cbn; lia | idtac]. 1: iSplitR; [iPureIntro; rewrite HarrayFact3; cbn; lia | idtac].
  1: zesu_expose_environment_alias. 1: iIntros (vmem) "%HframeRead8 %HframeReg8 HframeReturned". 1: time "return-frame-index0" (zesu_run_until ltac:(fun _ => lazymatch goal with | |- envs_entails _ (@iris.bi.interface.bi_exist _ nat _) => idtac end)). 1: iExists 0%nat.
  1: iSplitR; [iPureIntro; cbn; lia | idtac]. 1: iSplitR; [iPureIntro; rewrite HarrayFact3; cbn; lia | idtac]. 1: zesu_expose_environment_alias. 1: iIntros (vmem0) "%HframeRead0 %HframeReg0 HframeReturned0". 1: time "return-masked-handoff" (zesu_run_until ltac:(fun _ => lazymatch goal with | |- envs_entails _ (li_tactic (normalize_instr_addr _) _) => unLET; lazymatch goal with | |- envs_entails _ (li_tactic (normalize_instr_addr (bv_unsigned (bv_or _ _))) _) => idtac end end)). 1: unLET.
  1: replace (decodeItemStackPointer args - RlpDecodeItem.decodeItemStackBytes + 8 - (decodeItemStackPointer args - RlpDecodeItem.decodeItemStackBytes)) with 8 in HreturnReady by lia. 1: replace (decodeItemStackPointer args - RlpDecodeItem.decodeItemStackBytes + 0 - (decodeItemStackPointer args - RlpDecodeItem.decodeItemStackBytes)) with 0 in HframeReady by lia.
  1: cbn [N.to_nat] in HreturnReady. 1: cbn [N.to_nat] in HframeReady. 1: zesu_expose_environment_alias; rewrite HreturnReady HframeReady. 1: assert (HreturnLowBit : bv_extract 0 1 (Z_to_bv 64 (decodeItemReturnAddress args)) = BV 1 0) by (clear -HarrayFact23 HarrayFact24 HarrayFact25; unfold RlpDecodeItem.word64Modulus in *; bv_solve). 1: pose (decodeItemMaskedReturnAddress _ HreturnLowBit) as HmaskedReturn. 1: assert (HreturnAddZero : bv_add (Z_to_bv 64 (decodeItemReturnAddress args)) (BV 64 0) = Z_to_bv 64 (decodeItemReturnAddress args)) by bv_solve. 1: rewrite HreturnAddZero HmaskedReturn Z_to_bv_unsigned bv_wrap_small; last (unfold bv_modulus; change (0 <= decodeItemReturnAddress args < RlpDecodeItem.word64Modulus); lia). 1: notypeclasses refine (tac_li_tactic _ _ (normalize_instr_addr_hint (decodeItemReturnAddress args) (decodeItemReturnAddress args) eq_refl) _ _). 1: cbn [li_tactic_P normalize_instr_addr_hint]. 1: liFindInContext.
  1: iMatchHyp ltac:(fun name resource => lazymatch resource with | (?base ↦ₘ∗ ?values)%I => constr_eq base (decodeItemOutputPointer args); iExists values end). 1: iSplitR. 1: rename select (length (returnStorage locals) = _) into HstorageLength. 1: rename select (decodeItemLongAcceptedFacts args _ _ _) into Haccepted. 1: rename select (returnStorage locals = _) into HstorageBefore. 1: rename select (bv_unsigned (returnA1 locals) = _) into HreturnA1. 1: rename select (bv_unsigned (returnA3 locals) = _) into HreturnA3. 1: rename select (bv_unsigned (returnA4 locals) = _) into HreturnA4. 1: rename select (0 <= RlpDecodeItem.bigEndian _) into HpayloadNonnegative.   1: iPureIntro; split; [exact H0 | idtac]. 1: lazymatch goal with |- DecodeMeaningModuloKnownBugs args ?after => assert (HcanonicalImage : after = decodeItemOkBytes (returnStorage locals) (bv_to_little_endian 8 8 (bv_unsigned (returnA1 locals))) (bv_to_little_endian 8 8 (bv_unsigned (returnA3 locals))) (bv_to_little_endian 8 8 (bv_unsigned (returnA4 locals))) true) by (generalize HstorageLength; generalize (returnStorage locals); intros before Hlength; clear -before Hlength locals; do 40 (destruct before as [|? before]; [discriminate |]); destruct before; [unfold decodeItemOkBytes, bv_to_little_endian, Z_to_little_endian; cbn [Z.iter Pos.iter Z.of_N N.to_nat take drop firstn skipn list_fmap fmap insert]; repeat (rewrite Z.land_ones; last lia); repeat (rewrite Z.shiftr_div_pow2; last lia); reflexivity | cbn in Hlength; lia]) end.   1: rewrite HcanonicalImage. 1: eapply (decodeItemLongListPostMeaning args _ (1 + (bv_unsigned inputPrefix - 247)) (RlpDecodeItem.bigEndian (take (Z.to_nat (bv_unsigned inputPrefix - 247)) rest))). 1: exact (proj2 H0). 1: exact Haccepted. 1: rewrite <- HstorageBefore; apply decodeItemOkBytes_encodeSuccess. 1: exact HstorageLength. 1-3: apply length_bv_to_little_endian; compute; discriminate. 1: rewrite (littleEndian_machine_bytes 8); last (change (0 <= bv_unsigned (returnA1 locals) < bv_modulus 64); apply bv_unsigned_in_range). 1: rewrite HreturnA1; unfold RlpDecodeItemSchema.itemPayloadPointer; rewrite H3; cbn; assert (Hpneq : (bv_unsigned inputPrefix =? 128) = false) by (apply Z.eqb_neq; lia); rewrite Hpneq; reflexivity. 1: rewrite (littleEndian_machine_bytes 8); [exact HreturnA3 | change (0 <= bv_unsigned (returnA3 locals) < bv_modulus 64); apply bv_unsigned_in_range]. 1: rewrite (littleEndian_machine_bytes 8); [exact HreturnA4 | change (0 <= bv_unsigned (returnA4 locals) < bv_modulus 64); apply bv_unsigned_in_range]. 1: lia. 1: exact HpayloadNonnegative.   1: pose proof (decodeItemStackEpilogueRestored args) as HstackRestored. 1: rename select (length (returnFrame locals) = _) into HframeLength. 1: unfold decodeItemExitResources; rewrite HstackRestored; iFrame. 1: iRename select ((decodeItemStackPointer args - RlpDecodeItem.decodeItemStackBytes) ↦ₘ∗ _)%I into "HframeBytes". 1: iDestruct (IslarisMemory.mem_mapsto_byte_array_to_mapsto_len 16 with "HframeBytes") as "Hframe"; first exact HframeLength. 1: iSplitL "Hframe"; last done. 1: iApply (ghost_state.mem_mapsto_mapsto_to_uninit with "Hframe").
  1: unLET.
  1: assert (HreturnSecondBit : bv_extract 0 1 (bv_shiftr (bv_or (bv_and (bv_add (Z_to_bv 64 (decodeItemReturnAddress args)) (BV 64 0)) (BV 64 18446744073709551614)) (BV 64 0)) (BV 64 1)) = BV 1 0) by (clear -HarrayFact23 HarrayFact24 HarrayFact25; unfold RlpDecodeItem.word64Modulus in *; bv_simplify_arith; assert (Hlow : bv_extract 0 1 (Z_to_bv 64 (decodeItemReturnAddress args)) = BV 1 0) by bv_solve; pose proof (decodeItemMaskedReturnAddress (Z_to_bv 64 (decodeItemReturnAddress args)) Hlow) as Hmask; bv_simplify_arith Hmask; rewrite Z.add_0_r Hmask (bv_wrap_small 64 (decodeItemReturnAddress args)); last (change (0 <= decodeItemReturnAddress args < 2^64); lia); change ((decodeItemReturnAddress args / 2) mod 2 = 0); assert (Hmultiple : decodeItemReturnAddress args = (decodeItemReturnAddress args / 4 * 2) * 2) by (pose proof (Z.div_mod (decodeItemReturnAddress args) 4 ltac:(lia)); lia); rewrite Hmultiple Z.div_mul; last lia; apply Z.mod_mul; lia). 1: replace (decodeItemStackPointer args - RlpDecodeItem.decodeItemStackBytes + 8 - (decodeItemStackPointer args - RlpDecodeItem.decodeItemStackBytes)) with 8 in HreturnReady by lia. 1: cbn [N.to_nat] in HreturnReady. 1: rewrite HreturnReady HreturnSecondBit in H44; discriminate. Unshelve. all: try solve [lazymatch goal with |- SHELVED_SIDECOND _ => unshelve_sidecond end; repeat f_equal; first [reflexivity | apply proof_irrel | apply bool_decide_true; bv_solve | cbn [N.to_nat]; lia]].
  all: unshelve_sidecond.
  all: repeat first [rewrite length_app | rewrite length_cons | rewrite length_drop | rewrite length_take]; rewrite H2; cbn [N.to_nat]; lia.
Qed.
