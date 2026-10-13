Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.Approved.
Require Import ZesuSsz.Compliance.DecodeItemHints.
Require Import ZesuSsz.Compliance.DecodeItemReturnRestorationFacts.
Require Import ZesuSsz.Compliance.DecodeItemLongStringOutputMeaning.
Require Import ZesuSsz.Contracts.DecodeItemFrameImage.
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

Definition DesignedEntry_800d6a40
    `{!islaG Sigma} `{!threadG} (args : DecodeItemArgs) (locals : DecodeItemReturnLocals) (inputPrefix : byte) (rest : list byte) (headerLength : Z) (payloadLength : Z) : iProp Sigma :=
  ((ZesuSsz.Contracts.RlpDecodeItemBlockEntries.decodeItemEntryAt800d6a40 (args) (locals) (inputPrefix) (rest) (headerLength) (payloadLength)) ∗
   True)%I.
Global Instance : LithiumUnfold (@DesignedEntry_800d6a40) := I.
Global Typeclasses Opaque DesignedEntry_800d6a40.

Lemma DesignedBoundary_800d6a40 `{!islaG Sigma} `{!threadG} (args : DecodeItemArgs) (locals : DecodeItemReturnLocals) (inputPrefix : byte) (rest : list byte) (headerLength : Z) (payloadLength : Z)  :
  decodeItemSelectedCode -∗
  instr_body 0x800d6a40
    (DesignedEntry_800d6a40 args locals inputPrefix rest headerLength payloadLength).
Proof.
zesu_block. 2: apply find_mem_region_array.
1: left; unfold LET0; bv_simplify_arith; rewrite ?length_insert; cbn [length]; zesu_normalize_known_list_lengths. 1: rewrite !length_insert; zesu_normalize_known_list_lengths; cbn [N.to_nat]; rewrite bv_wrap_small; [lia | unfold bv_modulus, RlpDecodeItem.word64Modulus in *; cbn; lia].
cbn; iSplitR; [iPureIntro; reflexivity |]. iExists 24%nat.
iSplitR; [iPureIntro; bv_solve |]. iSplitR; [iPureIntro; cbn [length]; rewrite ?length_insert; zesu_normalize_known_list_lengths; cbn [N.to_nat]; lia |].
iIntros "?". zesu_block.
iDestruct select (∃ vact : valu, ⌜vact = RVal_Bool false⌝ ∗ "rv_enable_pmp" ↦ᵣ vact)%I as (pmpValue) "[%Hpmp ?]". subst pmpValue.
zesu_block. repeat (iDestruct select (∃ vact : valu, ⌜vact = _⌝ ∗ _)%I as (registerValue) "[%HregisterValue ?]"; subst registerValue).
zesu_block. unfold li_tactic, regcol_compute_hint.
iExists (false, ExactShape (RVal_Bits (Z_to_bv 64 9223372036854780160))). iSplitR; [iPureIntro; reflexivity |].
iSplitR; [iPureIntro; do 2 f_equal; apply (proj2 (bvn_eq _ _)); split; vm_compute; reflexivity |]. iIntros "HmisaCol".
zesu_run_until ltac:(fun _ => lazymatch goal with | |- envs_entails _ (find_in_context (FindStructRegMapsTo "mtvec" "bits") _) => idtac end). unfold IPM_JANNO.
ZesuSsz.Automation.Hooks.zesu_restore_register_collection "mtvec" "bits". ZesuSsz.Automation.Hooks.zesu_register_collection_selection_if_enabled.
unfold li_tactic, regcol_compute_hint. iExists (false, ExactShape (RVal_Bits (Z_to_bv 64 0))).
iSplitR; [iPureIntro; reflexivity |]. cbn; iSplitR; [iPureIntro; do 2 f_equal; apply (proj2 (bvn_eq _ _)); split; vm_compute; reflexivity |].
iIntros "HmtvecCol". zesu_block.
1: exact 8%nat. 1: prepare_sidecond; cbn; lia.
1: prepare_sidecond; cbn; rewrite HarrayFact3; lia. repeat (iDestruct select (∃ vact : valu, ⌜vact = _⌝ ∗ _)%I as (registerValue) "[%HregisterValue ?]"; subst registerValue).
ZesuSsz.Automation.Hooks.zesu_restore_register_collection "misa" "bits". ZesuSsz.Automation.Hooks.zesu_register_collection_selection_if_enabled.
unfold li_tactic, regcol_compute_hint. iExists (false, ExactShape (RVal_Bits (Z_to_bv 64 9223372036854780160))).
iSplitR; [iPureIntro; reflexivity |]. iSplitR; [iPureIntro; do 2 f_equal; apply (proj2 (bvn_eq _ _)); split; vm_compute; reflexivity |].
iIntros "HmisaReloadCol". zesu_run_until ltac:(fun _ => lazymatch goal with | |- envs_entails _ (find_in_context (FindStructRegMapsTo "mtvec" "bits") _) => idtac end).
unfold IPM_JANNO. ZesuSsz.Automation.Hooks.zesu_restore_register_collection "mtvec" "bits".
ZesuSsz.Automation.Hooks.zesu_register_collection_selection_if_enabled. unfold li_tactic, regcol_compute_hint.
iExists (false, ExactShape (RVal_Bits (Z_to_bv 64 0))). iSplitR; [iPureIntro; reflexivity |].
cbn; iSplitR; [iPureIntro; do 2 f_equal; apply (proj2 (bvn_eq _ _)); split; vm_compute; reflexivity |]. iIntros "HmtvecReloadCol".
zesu_run_until ltac:(fun _ => lazymatch goal with | |- envs_entails _ (find_in_context (FindMemMapsTo _) _) => idtac end). unfold IPM_JANNO.
repeat iDestruct select (_ ∗ _)%I as "[? ?]". ZesuSsz.Automation.Hooks.zesu_restore_register_collection "mstatus" "bits".
ZesuSsz.Automation.Hooks.zesu_register_collection_selection_if_enabled. zesu_block.
1: exact 0%nat. 1: prepare_sidecond; cbn; lia.
1: prepare_sidecond; cbn; rewrite HarrayFact3; lia. repeat (iDestruct select (∃ vact : valu, ⌜vact = _⌝ ∗ _)%I as (registerValue) "[%HregisterValue ?]"; subst registerValue).
ZesuSsz.Automation.Hooks.zesu_restore_register_collection "misa" "bits". ZesuSsz.Automation.Hooks.zesu_register_collection_selection_if_enabled.
unfold li_tactic, regcol_compute_hint. iExists (false, ExactShape (RVal_Bits (Z_to_bv 64 9223372036854780160))).
iSplitR; [iPureIntro; reflexivity |]. iSplitR; [iPureIntro; do 2 f_equal; apply (proj2 (bvn_eq _ _)); split; vm_compute; reflexivity |].
iIntros "HmisaReturnCol". zesu_run_until ltac:(fun _ => lazymatch goal with | |- envs_entails _ (find_in_context (FindStructRegMapsTo "mtvec" "bits") _) => idtac end).
unfold IPM_JANNO. ZesuSsz.Automation.Hooks.zesu_restore_register_collection "mtvec" "bits".
ZesuSsz.Automation.Hooks.zesu_register_collection_selection_if_enabled. unfold li_tactic, regcol_compute_hint.
iExists (false, ExactShape (RVal_Bits (Z_to_bv 64 0))). iSplitR; [iPureIntro; reflexivity |].
cbn; iSplitR; [iPureIntro; do 2 f_equal; apply (proj2 (bvn_eq _ _)); split; vm_compute; reflexivity |]. iIntros "HmtvecReturnCol".
zesu_run_until ltac:(fun _ => lazymatch goal with | |- envs_entails _ (li_tactic (normalize_instr_addr _) _) => unLET; lazymatch goal with | |- envs_entails _ (li_tactic (normalize_instr_addr (bv_unsigned (bv_or _ _))) _) => idtac end end). unfold IPM_JANNO.
repeat iDestruct select (_ ∗ _)%I as "[? ?]". ZesuSsz.Automation.Hooks.zesu_restore_register_collection "mstatus" "bits".
ZesuSsz.Automation.Hooks.zesu_register_collection_selection_if_enabled. zesu_run_until ltac:(fun _ => lazymatch goal with | |- envs_entails _ (li_tactic (normalize_instr_addr _) _) => unLET; lazymatch goal with | |- envs_entails _ (li_tactic (normalize_instr_addr (bv_unsigned (bv_or _ _))) _) => idtac end end).
1: pose proof (decodeItemReturnRestorationFacts args (returnFrame locals) H1) as Hrestoration. 1: unfold decodeItemReturnRestoration, decodeItemFrameAndStackRestoration in Hrestoration; destruct Hrestoration as (HreturnReady & HframeReady & HstackReady).
1: replace (decodeItemStackPointer args - RlpDecodeItem.decodeItemStackBytes + 8 - (decodeItemStackPointer args - RlpDecodeItem.decodeItemStackBytes))%Z with 8%Z in HreturnReady by lia. 1: replace (decodeItemStackPointer args - RlpDecodeItem.decodeItemStackBytes + 0 - (decodeItemStackPointer args - RlpDecodeItem.decodeItemStackBytes))%Z with 0%Z in HframeReady by lia.
1: cbn [N.to_nat] in HreturnReady, HframeReady. 1: rewrite HreturnReady HframeReady.
1: assert (HreturnLowBit : bv_extract 0 1 (Z_to_bv 64 (decodeItemReturnAddress args)) = BV 1 0) by (clear -HarrayFact23 HarrayFact24 HarrayFact25; unfold RlpDecodeItem.word64Modulus in *; bv_solve). 1: pose (decodeItemMaskedReturnAddress _ HreturnLowBit) as HmaskedReturn.
1: assert (HreturnAddZero : bv_add (Z_to_bv 64 (decodeItemReturnAddress args)) (BV 64 0) = Z_to_bv 64 (decodeItemReturnAddress args)) by bv_solve. 1: rewrite HreturnAddZero HmaskedReturn Z_to_bv_unsigned bv_wrap_small; last (unfold bv_modulus; change (0 <= decodeItemReturnAddress args < RlpDecodeItem.word64Modulus)%Z; lia).
1: notypeclasses refine (tac_li_tactic _ _ (normalize_instr_addr_hint (decodeItemReturnAddress args) (decodeItemReturnAddress args) eq_refl) _ _). 1: cbn [li_tactic_P normalize_instr_addr_hint].
1: liFindInContext. 1: iMatchHyp ltac:(fun name resource => lazymatch resource with | (?base ↦ₘ∗ ?values)%I => constr_eq base (decodeItemOutputPointer args); iExists values end).
1: iSplitR. 1: rename select (length (returnStorage locals) = _) into HstorageLength.
1: rename select (decodeItemLongAcceptedFacts args _ _ _) into Haccepted. 1: rename select (returnStorage locals = _) into HstorageBefore.
1: rename select (bv_unsigned (returnA1 locals) = _) into HreturnA1. 1: rename select (bv_unsigned (returnA3 locals) = _) into HreturnA3.
1: rename select (bv_unsigned (returnA4 locals) = _) into HreturnA4. 1: rename select ((0 <= RlpDecodeItem.bigEndian _)%Z) into HpayloadNonnegative.
1: iPureIntro; split; [exact H0 | idtac]. 1: lazymatch goal with |- DecodeMeaningModuloKnownBugs args ?after => assert (HcanonicalImage : after = decodeItemOkBytes (returnStorage locals) (bv_to_little_endian 8 8 (bv_unsigned (returnA1 locals))) (bv_to_little_endian 8 8 (bv_unsigned (returnA3 locals))) (bv_to_little_endian 8 8 (bv_unsigned (returnA4 locals))) false) by (generalize HstorageLength; generalize (returnStorage locals); intros before Hlength; clear -before Hlength locals; do 40 (destruct before as [|? before]; [discriminate |]); destruct before; [unfold decodeItemOkBytes, bv_to_little_endian, Z_to_little_endian; cbn [Z.iter Pos.iter Z.of_N N.to_nat take drop firstn skipn list_fmap fmap insert]; repeat (rewrite Z.land_ones; last lia); repeat (rewrite Z.shiftr_div_pow2; last lia); assert (Hwidth8 : N.to_nat 8%N = 8%nat) by (vm_compute; reflexivity); assert (Hwidth2 : N.to_nat 2%N = 2%nat) by (vm_compute; reflexivity); assert (Hzero64 : bv_unsigned (0%bv : bv 64) = 0%Z) by (vm_compute; reflexivity); rewrite ?Hwidth8 ?Hwidth2 ?Hzero64; cbn; assert (Hzero8 : (0%bv : bv 8) = Z_to_bv 8 0%Z) by (apply (proj2 (bv_eq 8 _ _)); split; vm_compute; reflexivity); change (0 `mod` 2 ^ 8)%Z with 0%Z; rewrite ?Hzero8; reflexivity | cbn in Hlength; lia]) end.
1: apply (decodeItemLongStringMachineOutputMeaning args locals inputPrefix rest _); unfold decodeItemLongStringMachineMeaningFacts; pose proof (proj2 H0) as Hdomain; repeat first [assumption | split | lia]. 1: pose proof (decodeItemStackEpilogueRestored args) as HstackRestored.
1: rename select (length (returnFrame locals) = _) into HframeLength. 1: unfold decodeItemExitResources; rewrite HstackRestored; iFrame.
1: iRename select ((decodeItemStackPointer args - RlpDecodeItem.decodeItemStackBytes) ↦ₘ∗ _)%I into "HframeBytes". 1: iDestruct (IslarisMemory.mem_mapsto_byte_array_to_mapsto_len 16 with "HframeBytes") as "Hframe"; first exact HframeLength.
1: iSplitR "Hframe". 2: iApply (ghost_state.mem_mapsto_mapsto_to_uninit with "Hframe").
1: repeat progress zesu_finish. 1: rewrite reg_col_cons reg_col_nil; iFrame.
1: cbn; repeat iDestruct select (_ ∗ _)%I as "[? ?]"; iFrame; done. unLET.
pose proof (decodeItemSavedReturnDecoder args (returnFrame locals) H1) as HfaultReturnReady. replace (decodeItemStackPointer args - RlpDecodeItem.decodeItemStackBytes + 8 - (decodeItemStackPointer args - RlpDecodeItem.decodeItemStackBytes))%Z with 8%Z in HfaultReturnReady by lia.
cbn [N.to_nat] in HfaultReturnReady. rewrite HfaultReturnReady in H79.
assert (HreturnSecondBit : bv_extract 0 1 (bv_shiftr (bv_or (bv_and (bv_add (Z_to_bv 64 (decodeItemReturnAddress args)) (BV 64 0)) (BV 64 18446744073709551614)) (BV 64 0)) (BV 64 1)) = BV 1 0) by (clear -HarrayFact23 HarrayFact24 HarrayFact25; unfold RlpDecodeItem.word64Modulus in *; bv_simplify_arith; assert (Hlow : bv_extract 0 1 (Z_to_bv 64 (decodeItemReturnAddress args)) = BV 1 0) by bv_solve; pose proof (decodeItemMaskedReturnAddress (Z_to_bv 64 (decodeItemReturnAddress args)) Hlow) as Hmask; bv_simplify_arith Hmask; rewrite Z.add_0_r Hmask (bv_wrap_small 64 (decodeItemReturnAddress args)); last (change (0 <= decodeItemReturnAddress args < 2^64)%Z; lia); change ((decodeItemReturnAddress args / 2) mod 2 = 0)%Z; assert (Hmultiple : (decodeItemReturnAddress args = (decodeItemReturnAddress args / 4 * 2) * 2)%Z) by (pose proof (Z.div_mod (decodeItemReturnAddress args) 4 ltac:(lia)); lia); rewrite Hmultiple Z.div_mul; last lia; apply Z.mod_mul; lia). rewrite HreturnSecondBit in H79; discriminate.
Unshelve. unshelve_sidecond; f_equal; apply bool_decide_true; bv_solve.
Qed.
