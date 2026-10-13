Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Proofs.DecodeItem.Hand.Common.
Require Import ZesuSsz.Automation.Approved.
Require Import ZesuSsz.Compliance.DecodeItemHints.

Set Printing Width 200.
Require Import isla.isla.
From iris.proofmode Require Import environments.
Require Import ZesuSsz.Stock.Closure.index_decodeItem.
Require Import ZesuSsz.Contracts.RlpDecodeItemFoldEntries.
Require Import ZesuSsz.Contracts.DecodeItemReturnFacts.
Require Import ZesuSsz.Contracts.RlpDecodeItemByteFold.
Require Import ZesuSsz.Contracts.RlpDecodeItemByteFoldBlocks.
Require Import ZesuSsz.Automation.SealedCoverage.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Require Import ZesuSsz.Contracts.DecodeItemSelected.
Require Import SailStdpp.MachineWord.
Require Import ZesuSsz.Automation.ReturnWand.
Require Import ZesuSsz.Automation.ReturnWand.
(* Native successor capture; no resources added. *)
Require Import ZesuSsz.Automation.SealedCoverage.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.RlpDecodeItemFoldEntries.
Require Import ZesuSsz.Contracts.DecodeItemReturnFacts.
Require Import ZesuSsz.Contracts.RlpDecodeItemByteFold.
Require Import ZesuSsz.Contracts.RlpDecodeItemByteFoldBlocks.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Require Import ZesuSsz.Contracts.DecodeItemSelected.
Require Import SailStdpp.MachineWord.
Require Import ZesuSsz.Automation.ReturnWand.

Definition DesignedEntry_800d6a24
    `{!islaG Sigma} `{!threadG} (args : DecodeItemArgs) (inputPrefix : byte) (rest : list byte) : iProp Sigma :=
  ((ZesuSsz.Contracts.RlpDecodeItemFoldEntries.decodeItemEntryAt800d6a24 (args) (inputPrefix) (rest)) ∗
   True)%I.
Global Instance : LithiumUnfold (@DesignedEntry_800d6a24) := I.
Global Typeclasses Opaque DesignedEntry_800d6a24.


Require Import ZesuSsz.Contracts.RlpDecodeItemFoldEntries.
Require Import ZesuSsz.Contracts.DecodeItemReturnFacts.
Require Import ZesuSsz.Contracts.RlpDecodeItemByteFold.
Require Import ZesuSsz.Contracts.RlpDecodeItemByteFoldBlocks.
Require Import ZesuSsz.Contracts.DecodeItemBranchEntries.
Local Ltac hand_fold_recover count := let rec run remaining := lazymatch remaining with | O => idtac | S ?next => only 1: zesu_liAStep; run next end in run count.
Lemma DesignedBoundary_800d6a24 `{!islaG Sigma} `{!threadG} (args : DecodeItemArgs) (inputPrefix : byte) (rest : list byte)   :
  instr_pre 0x800d6a38 (∃ (successor_n : Z) (successor_payloadStart : Z) (successor_lengthBytes : list byte) (successor_frameBytes : list byte) (successor_loaded : bv 64) (successor_inputPrefix : byte) (successor_rest : list byte), ZesuSsz.Contracts.DecodeItemBranchEntries.decodeItemEntryAt800d6a38 (args) (successor_n) (successor_payloadStart) (successor_lengthBytes) (successor_frameBytes) (successor_loaded) (successor_inputPrefix) (successor_rest))%I -∗
  instr_pre 0x800d6a24 (∃ (successor_inputPrefix : byte) (successor_rest : list byte), ZesuSsz.Contracts.RlpDecodeItemFoldEntries.decodeItemEntryAt800d6a24 (args) (successor_inputPrefix) (successor_rest))%I -∗
  decodeItemSelectedCode -∗
  instr_body 0x800d6a24
    (DesignedEntry_800d6a24 args inputPrefix rest).
Proof.
iStartProof; ZesuSsz.Automation.Finish.zesu_expose_code_lists; repeat first [progress iIntros (?) | progress iIntros "#?" | progress iIntros "?"]; ZesuSsz.Automation.Finish.zesu_reduce_introduced_code_lists; repeat iDestruct select (_ ∗ _)%I as "[? ?]".
1: ltac2:(let rec run count := if Int.gt count 0 then (Control.focus 1 1 (fun () => ltac1:(tryif lazymatch goal with | |- envs_entails _ (@bi_exist _ _ _) => idtac | |- nat => idtac | |- list (bv 8) => idtac end then fail "HAND-WITNESS-FRONTIER" else zesu_liAStep)); run (Int.sub count 1)) else () in run 120).
iExists (Val_Bits (bv_and b 131072)); iSplit; [done|].
1: hand_fold_recover constr:(3%nat).
iExists (Val_Bool (bool_decide (bv_and b 131072 = 0%bv))); iSplit; [done|].
1: hand_fold_recover constr:(61%nat).
1: iExists LET1; iSplit; [done|].
1: hand_fold_recover constr:(12%nat).
1: iExists LET2; iSplit; [done|].
1: hand_fold_recover constr:(12%nat).
1: iExists (Z.to_nat (1 + i)); iSplit; [iPureIntro; exact (decodeItemFoldArrayIndex args n i payloadStart lengthBytes H5)|].
1: iSplit; [iPureIntro; pose proof H5 as Hfold; destruct Hfold as (Hwidth & Hindex & Hstart & Hbytes & HlengthBytes & Hfit); pose proof (proj1 (proj2 H1)) as HinputLength; lia|].
1: iExists eq_refl.
1: hand_fold_recover constr:(20%nat).
1: iExists LET; iFrame.
1: hand_fold_recover constr:(24%nat).
1: iExists (Val_Bits (bv_and b0 131072)); iSplit; [done|].
1: hand_fold_recover constr:(3%nat).
1: iExists (Val_Bool (bool_decide (bv_and b0 131072 = 0%bv))); iSplit; [done|].
1: hand_fold_recover constr:(38%nat).
1: iExists LET3; iFrame.
1: hand_fold_recover constr:(24%nat).
1: iExists (Val_Bits (bv_and b1 131072)); iSplit; [done|].
1: hand_fold_recover constr:(3%nat).
1: iExists (Val_Bool (bool_decide (bv_and b1 131072 = 0%bv))); iSplit; [done|].
1: hand_fold_recover constr:(38%nat).
1: iExists LET5; iFrame.
1: hand_fold_recover constr:(24%nat).
1: iExists (Val_Bits (bv_and b2 131072)); iSplit; [done|].
1: hand_fold_recover constr:(3%nat).
1: iExists (Val_Bool (bool_decide (bv_and b2 131072 = 0%bv))); iSplit; [done|].
1: hand_fold_recover constr:(48%nat).
1: iExists LET7; iFrame.
1: hand_fold_recover constr:(42%nat).
1: iExists (Val_Bits (bv_and b3 131072)); iSplit; [done|].
1: hand_fold_recover constr:(3%nat).
1: iExists (Val_Bool (bool_decide (bv_and b3 131072 = 0%bv))); iSplit; [done|].
1: hand_fold_recover constr:(47%nat).
1: iExists LET10; iSplit; [done|].
1: hand_fold_recover constr:(16%nat).
1: iExists LET13; iSplit; [done|].
1: hand_fold_recover constr:(10%nat).
1: iExists LET11; iFrame.
1: hand_fold_recover constr:(2%nat).
1: assert (Hnext : nth_error (decodeItemInputBytes args) (Z.to_nat (1 + i)) = Some vmem) by (rewrite decodeItemListLookupNthError; exact H10).
1: pose proof (decodeItemFoldSteppedCursor args _ _ _ _ H5) as HsteppedCursor.
1: pose proof (decodeItemFoldSteppedAccumulator args _ _ _ _ vmem H5 H0 Hnext) as HsteppedAccumulator.
1: assert (HsuccessorLe : i + 1 <= bv_unsigned inputPrefix - 183) by (rewrite Z.add_1_r; apply Zlt_le_succ; exact H0).
1: assert (HsuccessorNe : i + 1 <> bv_unsigned inputPrefix - 183) by (intro Heq; apply H16; unfold LET6; rewrite HsteppedCursor; rewrite Heq; reflexivity).
1: assert (HsuccessorGuard : i + 1 < bv_unsigned inputPrefix - 183) by (destruct (proj1 (Z.lt_eq_cases _ _) HsuccessorLe) as [Hlt | Heq]; [exact Hlt | exfalso; exact (HsuccessorNe Heq)]).
1: pose proof (proj1 (ZesuSsz.Proofs.DecodeItem.ByteFoldPure.decodeItem_fold_preservation args _ _ _ _ vmem H5 H0 (decodeItemFoldByteAtSuccessor args _ _ _ _ vmem H5 H0 Hnext))) as HsteppedFold.
1: hand_repack_loop
  ltac:(iExists inputPrefix, rest; unfold decodeItemEntryAt800d6a24; iExists (bv_unsigned inputPrefix - 183), (i + 1), (decodeItemInputPointer args + 1), (take (Z.to_nat (bv_unsigned inputPrefix - 183)) (drop 1 (decodeItemInputBytes args))), frameBytes, LET0)
  constr:(conj HsuccessorGuard (conj H1 (conj H2 H3)))
  ltac:(iEval (unfold decodeItemByteFoldStringHeader, decodeItemByteFoldResources; rewrite -HsteppedAccumulator -HsteppedCursor))
  ltac:(idtac)
  constr:(conj H4 HsteppedFold)
  ltac:(unfold decodeItemBranchContinuation, decodeItemBranchContinuationAt).
1: zesu_block.
1: hand_fold_recover constr:(3%nat).
1: multimatch goal with | |- context[Val_Bool ?chosen] => is_evar chosen; hand_witness_at_evar constr:(0%nat) chosen ltac:(unify chosen (negb LET10)) ltac:(iSplit; [done|]) end.
1: hand_fold_recover constr:(11%nat).
1: iExists LET9; iFrame.
1: hand_fold_recover constr:(2%nat).
1: pose proof (decodeItemFoldExitIndex args _ _ _ _ H5 H0 HarrayFact21 HarrayFact23 H16) as HcompletedIndex.
1: pose proof (decodeItemFoldExitAccumulator args _ _ _ _ vmem H5 H0 HarrayFact21 HarrayFact23 H16 H10) as HcompletedAccumulator.
1: assert (Hnext : nth_error (decodeItemInputBytes args) (Z.to_nat (1 + i)) = Some vmem) by (rewrite decodeItemListLookupNthError; exact H10).
1: pose proof (proj1 (ZesuSsz.Proofs.DecodeItem.ByteFoldPure.decodeItem_fold_preservation args _ _ _ _ vmem H5 H0 (decodeItemFoldByteAtSuccessor args _ _ _ _ vmem H5 H0 Hnext))) as HcompletedFold; rewrite HcompletedIndex in HcompletedFold.
1: hand_repack_loop
  ltac:(iExists (bv_unsigned inputPrefix - 183), (decodeItemInputPointer args + 1), (take (Z.to_nat (bv_unsigned inputPrefix - 183)) (drop 1 (decodeItemInputBytes args))), frameBytes, LET0, inputPrefix, rest; unfold decodeItemEntryAt800d6a38)
  constr:(conj (proj2 H1) (conj H3 H2))
  ltac:(iEval (unfold decodeItemByteFoldResources; rewrite -HcompletedAccumulator -H16))
  ltac:(iEval (rewrite H16))
  constr:(conj H4 HcompletedFold)
  ltac:(unfold decodeItemBranchContinuation, decodeItemBranchContinuationAt).
1: hand_fold_recover constr:(2%nat).
1: iExists (li_pair (negb LET1) tt); iSplit; [done|].
1: hand_fold_recover constr:(12%nat).
1: hand_fold_recover constr:(2%nat).
1: iExists (li_pair LET2 tt); iSplit; [done|].
1: iIntros (Hmetadata); cbn in Hmetadata; unfold LET2 in Hmetadata; apply (bool_decide_eq_true_1 (bv_zero_extend 128 LET0 = 1073741824%bv)) in Hmetadata; exfalso; exact (decodeItemFoldInputBaseGuardImpossible args n i payloadStart lengthBytes H5 H0 (proj2 H1) Hmetadata).
1: ltac2:(let rec run count := if Int.gt count 0 then (Control.focus 1 1 (fun () => ltac1:(tryif lazymatch goal with | |- envs_entails _ (@bi_exist _ _ _) => idtac | |- nat => idtac | |- list (bv 8) => idtac end then fail "HAND-WITNESS-FRONTIER" else zesu_liAStep)); run (Int.sub count 1)) else () in run 2).
1: iExists (negb LET2); iSplit; [done|].
1: ltac2:(let rec run count := if Int.gt count 0 then (Control.focus 1 1 (fun () => ltac1:(tryif lazymatch goal with | |- envs_entails _ (@bi_exist _ _ _) => idtac | |- nat => idtac | |- list (bv 8) => idtac end then fail "HAND-WITNESS-FRONTIER" else zesu_liAStep)); run (Int.sub count 1)) else () in run 13).
1: iExists LET3; iSplit; [done|].
1: ltac2:(let rec run count := if Int.gt count 0 then (Control.focus 1 1 (fun () => ltac1:(tryif lazymatch goal with | |- envs_entails _ (@bi_exist _ _ _) => idtac | |- nat => idtac | |- list (bv 8) => idtac end then fail "HAND-WITNESS-FRONTIER" else zesu_liAStep)); run (Int.sub count 1)) else () in run 12).
1: iExists LET4; iSplit; [done|].
1: ltac2:(let rec run count := if Int.gt count 0 then (Control.focus 1 1 (fun () => ltac1:(tryif lazymatch goal with | |- envs_entails _ (@bi_exist _ _ _) => idtac | |- nat => idtac | |- list (bv 8) => idtac end then fail "HAND-WITNESS-FRONTIER" else zesu_liAStep)); run (Int.sub count 1)) else () in run 23).
1: iExists LET5; iSplit; [done|].
1: ltac2:(let rec run count := if Int.gt count 0 then (Control.focus 1 1 (fun () => ltac1:(tryif lazymatch goal with | |- envs_entails _ (@bi_exist _ _ _) => idtac | |- nat => idtac | |- list (bv 8) => idtac end then fail "HAND-WITNESS-FRONTIER" else zesu_liAStep)); run (Int.sub count 1)) else () in run 12).
1: iExists (Z.to_nat (1 + i)); iSplit; [iPureIntro; exact (decodeItemFoldArrayIndex args n i payloadStart lengthBytes H5)|].
1: ltac2:(let rec run count := if Int.gt count 0 then (Control.focus 1 1 (fun () => ltac1:(tryif lazymatch goal with | |- envs_entails _ (@bi_exist _ _ _) => idtac | |- nat => idtac | |- list (bv 8) => idtac end then fail "HAND-WITNESS-FRONTIER" else zesu_liAStep)); run (Int.sub count 1)) else () in run 1).
1: iExists eq_refl.
1: ltac2:(let rec run count := if Int.gt count 0 then (Control.focus 1 1 (fun () => ltac1:(tryif lazymatch goal with | |- envs_entails _ (@bi_exist _ _ _) => idtac | |- nat => idtac | |- list (bv 8) => idtac end then fail "HAND-WITNESS-FRONTIER" else zesu_liAStep)); run (Int.sub count 1)) else () in run 20).
1: iExists LET; iFrame.
1: ltac2:(let rec run count := if Int.gt count 0 then (Control.focus 1 1 (fun () => ltac1:(tryif lazymatch goal with | |- envs_entails _ (@bi_exist _ _ _) => idtac | |- nat => idtac | |- list (bv 8) => idtac end then fail "HAND-WITNESS-FRONTIER" else zesu_liAStep)); run (Int.sub count 1)) else () in run 24).
1: iExists (Val_Bits (bv_and b0 131072)); iSplit; [done|].
1: ltac2:(let rec run count := if Int.gt count 0 then (Control.focus 1 1 (fun () => ltac1:(tryif lazymatch goal with | |- envs_entails _ (@bi_exist _ _ _) => idtac | |- nat => idtac | |- list (bv 8) => idtac end then fail "HAND-WITNESS-FRONTIER" else zesu_liAStep)); run (Int.sub count 1)) else () in run 3).
1: iExists (Val_Bool (bool_decide (bv_and b0 131072 = 0%bv))); iSplit; [done|].
1: ltac2:(let rec run count := if Int.gt count 0 then (Control.focus 1 1 (fun () => ltac1:(tryif lazymatch goal with | |- envs_entails _ (@bi_exist _ _ _) => idtac | |- nat => idtac | |- list (bv 8) => idtac end then fail "HAND-WITNESS-FRONTIER" else zesu_liAStep)); run (Int.sub count 1)) else () in run 38).
1: iExists LET6; iFrame.
1: ltac2:(let rec run count := if Int.gt count 0 then (Control.focus 1 1 (fun () => ltac1:(tryif lazymatch goal with | |- envs_entails _ (@bi_exist _ _ _) => idtac | |- nat => idtac | |- list (bv 8) => idtac end then fail "HAND-WITNESS-FRONTIER" else zesu_liAStep)); run (Int.sub count 1)) else () in run 24).
1: iExists (Val_Bits (bv_and b1 131072)); iSplit; [done|].
1: ltac2:(let rec run count := if Int.gt count 0 then (Control.focus 1 1 (fun () => ltac1:(tryif lazymatch goal with | |- envs_entails _ (@bi_exist _ _ _) => idtac | |- nat => idtac | |- list (bv 8) => idtac end then fail "HAND-WITNESS-FRONTIER" else zesu_liAStep)); run (Int.sub count 1)) else () in run 3).
1: iExists (Val_Bool (bool_decide (bv_and b1 131072 = 0%bv))); iSplit; [done|].
1: ltac2:(let rec run count := if Int.gt count 0 then (Control.focus 1 1 (fun () => ltac1:(tryif lazymatch goal with | |- envs_entails _ (@bi_exist _ _ _) => idtac | |- nat => idtac | |- list (bv 8) => idtac end then fail "HAND-WITNESS-FRONTIER" else zesu_liAStep)); run (Int.sub count 1)) else () in run 38).
1: iExists LET8; iFrame.
1: ltac2:(let rec run count := if Int.gt count 0 then (Control.focus 1 1 (fun () => ltac1:(tryif lazymatch goal with | |- envs_entails _ (@bi_exist _ _ _) => idtac | |- nat => idtac | |- list (bv 8) => idtac end then fail "HAND-WITNESS-FRONTIER" else zesu_liAStep)); run (Int.sub count 1)) else () in run 24).
1: iExists (Val_Bits (bv_and b2 131072)); iSplit; [done|].
1: ltac2:(let rec run count := if Int.gt count 0 then (Control.focus 1 1 (fun () => ltac1:(tryif lazymatch goal with | |- envs_entails _ (@bi_exist _ _ _) => idtac | |- nat => idtac | |- list (bv 8) => idtac end then fail "HAND-WITNESS-FRONTIER" else zesu_liAStep)); run (Int.sub count 1)) else () in run 3).
1: iExists (Val_Bool (bool_decide (bv_and b2 131072 = 0%bv))); iSplit; [done|].
1: ltac2:(let rec run count := if Int.gt count 0 then (Control.focus 1 1 (fun () => ltac1:(tryif lazymatch goal with | |- envs_entails _ (@bi_exist _ _ _) => idtac | |- nat => idtac | |- list (bv 8) => idtac end then fail "HAND-WITNESS-FRONTIER" else zesu_liAStep)); run (Int.sub count 1)) else () in run 48).
1: iExists LET10; iFrame.
1: ltac2:(let rec run count := if Int.gt count 0 then (Control.focus 1 1 (fun () => ltac1:(tryif lazymatch goal with | |- envs_entails _ (@bi_exist _ _ _) => idtac | |- nat => idtac | |- list (bv 8) => idtac end then fail "HAND-WITNESS-FRONTIER" else zesu_liAStep)); run (Int.sub count 1)) else () in run 42).
1: iExists (Val_Bits (bv_and b3 131072)); iSplit; [done|].
1: ltac2:(let rec run count := if Int.gt count 0 then (Control.focus 1 1 (fun () => ltac1:(tryif lazymatch goal with | |- envs_entails _ (@bi_exist _ _ _) => idtac | |- nat => idtac | |- list (bv 8) => idtac end then fail "HAND-WITNESS-FRONTIER" else zesu_liAStep)); run (Int.sub count 1)) else () in run 3).
1: iExists (Val_Bool (bool_decide (bv_and b3 131072 = 0%bv))); iSplit; [done|].
1: ltac2:(let rec run count := if Int.gt count 0 then (Control.focus 1 1 (fun () => ltac1:(tryif lazymatch goal with | |- envs_entails _ (@bi_exist _ _ _) => idtac | |- nat => idtac | |- list (bv 8) => idtac end then fail "HAND-WITNESS-FRONTIER" else zesu_liAStep)); run (Int.sub count 1)) else () in run 47).
1: iExists LET13; iSplit; [done|].
1: ltac2:(let rec run count := if Int.gt count 0 then (Control.focus 1 1 (fun () => ltac1:(tryif lazymatch goal with | |- envs_entails _ (@bi_exist _ _ _) => idtac | |- nat => idtac | |- list (bv 8) => idtac end then fail "HAND-WITNESS-FRONTIER" else zesu_liAStep)); run (Int.sub count 1)) else () in run 16).
1: iExists LET16; iSplit; [done|].
1: ltac2:(let rec run count := if Int.gt count 0 then (Control.focus 1 1 (fun () => ltac1:(tryif lazymatch goal with | |- envs_entails _ (@bi_exist _ _ _) => idtac | |- nat => idtac | |- list (bv 8) => idtac end then fail "HAND-WITNESS-FRONTIER" else zesu_liAStep)); run (Int.sub count 1)) else () in run 10).
1: iExists LET14; iFrame.
1: ltac2:(let rec run count := if Int.gt count 0 then (Control.focus 1 1 (fun () => ltac1:(tryif lazymatch goal with | |- envs_entails _ (@bi_exist _ _ _) => idtac | |- nat => idtac | |- list (bv 8) => idtac end then fail "HAND-WITNESS-FRONTIER" else zesu_liAStep)); run (Int.sub count 1)) else () in run 2).
1: assert (Hnext : nth_error (decodeItemInputBytes args) (Z.to_nat (1 + i)) = Some vmem) by (rewrite decodeItemListLookupNthError; exact H13).
1: pose proof (decodeItemFoldSteppedCursor args _ _ _ _ H5) as HsteppedCursor.
1: pose proof (decodeItemFoldSteppedAccumulator args _ _ _ _ vmem H5 H0 Hnext) as HsteppedAccumulator.
1: assert (HsuccessorLe : i + 1 <= bv_unsigned inputPrefix - 183) by (rewrite Z.add_1_r; apply Zlt_le_succ; exact H0).
1: assert (HsuccessorNe : i + 1 <> bv_unsigned inputPrefix - 183) by (intro Heq; apply H19; unfold LET9; rewrite HsteppedCursor; rewrite Heq; reflexivity).
1: assert (HsuccessorGuard : i + 1 < bv_unsigned inputPrefix - 183) by (destruct (proj1 (Z.lt_eq_cases _ _) HsuccessorLe) as [Hlt | Heq]; [exact Hlt | exfalso; exact (HsuccessorNe Heq)]).
1: pose proof (proj1 (ZesuSsz.Proofs.DecodeItem.ByteFoldPure.decodeItem_fold_preservation args _ _ _ _ vmem H5 H0 (decodeItemFoldByteAtSuccessor args _ _ _ _ vmem H5 H0 Hnext))) as HsteppedFold.
1: hand_repack_loop
  ltac:(iExists inputPrefix, rest; unfold decodeItemEntryAt800d6a24; iExists (bv_unsigned inputPrefix - 183), (i + 1), (decodeItemInputPointer args + 1), (take (Z.to_nat (bv_unsigned inputPrefix - 183)) (drop 1 (decodeItemInputBytes args))), frameBytes, LET0)
  constr:(conj HsuccessorGuard (conj H1 (conj H2 H3)))
  ltac:(iEval (unfold decodeItemByteFoldStringHeader, decodeItemByteFoldResources; rewrite -HsteppedAccumulator -HsteppedCursor))
  ltac:(idtac)
  constr:(conj H4 HsteppedFold)
  ltac:(unfold decodeItemBranchContinuation, decodeItemBranchContinuationAt).
1: zesu_block.
1: ltac2:(let rec run count := if Int.gt count 0 then (Control.focus 1 1 (fun () => ltac1:(tryif lazymatch goal with | |- envs_entails _ (@bi_exist _ _ _) => idtac | |- nat => idtac | |- list (bv 8) => idtac end then fail "HAND-WITNESS-FRONTIER" else zesu_liAStep)); run (Int.sub count 1)) else () in run 3).
1: iExists (negb LET13); iSplit; [done|].
1: ltac2:(let rec run count := if Int.gt count 0 then (Control.focus 1 1 (fun () => ltac1:(tryif lazymatch goal with | |- envs_entails _ (@bi_exist _ _ _) => idtac | |- nat => idtac | |- list (bv 8) => idtac end then fail "HAND-WITNESS-FRONTIER" else zesu_liAStep)); run (Int.sub count 1)) else () in run 11).
1: iExists LET12; iFrame.
1: ltac2:(let rec run count := if Int.gt count 0 then (Control.focus 1 1 (fun () => ltac1:(tryif lazymatch goal with | |- envs_entails _ (@bi_exist _ _ _) => idtac | |- nat => idtac | |- list (bv 8) => idtac end then fail "HAND-WITNESS-FRONTIER" else zesu_liAStep)); run (Int.sub count 1)) else () in run 2).
1: pose proof (decodeItemFoldExitIndex args _ _ _ _ H5 H0 HarrayFact21 HarrayFact23 H19) as HcompletedIndex.
1: pose proof (decodeItemFoldExitAccumulator args _ _ _ _ vmem H5 H0 HarrayFact21 HarrayFact23 H19 H13) as HcompletedAccumulator.
1: assert (Hnext : nth_error (decodeItemInputBytes args) (Z.to_nat (1 + i)) = Some vmem) by (rewrite decodeItemListLookupNthError; exact H13).
1: pose proof (proj1 (ZesuSsz.Proofs.DecodeItem.ByteFoldPure.decodeItem_fold_preservation args _ _ _ _ vmem H5 H0 (decodeItemFoldByteAtSuccessor args _ _ _ _ vmem H5 H0 Hnext))) as HcompletedFold; rewrite HcompletedIndex in HcompletedFold.
1: hand_repack_loop
  ltac:(iExists (bv_unsigned inputPrefix - 183), (decodeItemInputPointer args + 1), (take (Z.to_nat (bv_unsigned inputPrefix - 183)) (drop 1 (decodeItemInputBytes args))), frameBytes, LET0, inputPrefix, rest; unfold decodeItemEntryAt800d6a38)
  constr:(conj (proj2 H1) (conj H3 H2))
  ltac:(iEval (unfold decodeItemByteFoldResources; rewrite -HcompletedAccumulator -H19))
  ltac:(iEval (rewrite H19))
  constr:(conj H4 HcompletedFold)
  ltac:(unfold decodeItemBranchContinuation, decodeItemBranchContinuationAt).
all: zesu_block.
Unshelve.
all: zesu_finish_v1.
Qed.
