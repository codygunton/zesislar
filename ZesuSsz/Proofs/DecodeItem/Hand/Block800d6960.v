Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Proofs.DecodeItem.Hand.Common.
Require Import ZesuSsz.Compliance.DecodeItemSavedFrameWitnesses.
Require Import ZesuSsz.Compliance.DecodeItemReturnRestorationFacts.
Require Import ZesuSsz.Compliance.DecodeItemMaskedReturnFacts.
Require Import ZesuSsz.Automation.PureFacts.
Require Import ZesuSsz.Automation.Approved.
Require Import ZesuSsz.Compliance.DecodeItemHints.

Set Printing Width 200.
Require Import isla.isla.
From iris.proofmode Require Import environments.
Require Import ZesuSsz.Stock.Closure.index_decodeItem.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Require Import ZesuSsz.Contracts.DecodeItemBranchEntries.
Require Import ZesuSsz.Automation.SealedCoverage.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.DecodeItemSelected.
Require Import SailStdpp.MachineWord.
Require Import ZesuSsz.Automation.ReturnWand.
Require Import ZesuSsz.Automation.ReturnWand.
(* Native successor capture; no resources added. *)
Require Import ZesuSsz.Automation.SealedCoverage.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Require Import ZesuSsz.Contracts.DecodeItemSelected.
Require Import SailStdpp.MachineWord.
Require Import ZesuSsz.Automation.ReturnWand.

Definition DesignedEntry_800d6960
    `{!islaG Sigma} `{!threadG} (returnAddress : Z) (args : DecodeItemArgs) : iProp Sigma :=
  ((ZesuSsz.Contracts.DecodeItemBranchEntries.decodeItemEntryAt800d6960 (returnAddress) (args)) ∗
   True)%I.
Global Instance : LithiumUnfold (@DesignedEntry_800d6960) := I.
Global Typeclasses Opaque DesignedEntry_800d6960.


Require Import ZesuSsz.Contracts.RlpDecodeItemBlockEntries.
Require Import ZesuSsz.Contracts.DecodeItemReturnFacts.
Require Import ZesuSsz.Contracts.RlpDecodeItemReturnImageDef.
Require Import ZesuSsz.Contracts.RlpDecodeItemReturnImages.
Require Import ZesuSsz.Contracts.DecodeItemBranchEntries.
Lemma DesignedBoundary_800d6960 `{!islaG Sigma} `{!threadG} (returnAddress : Z) (args : DecodeItemArgs)   :
  instr_pre 0x800d6974 (∃ (successor_frameBytes : list byte) (successor_inputPrefix : byte) (successor_rest : list byte), ZesuSsz.Contracts.DecodeItemBranchEntries.decodeItemEntryAt800d6974 (args) (successor_frameBytes) (successor_inputPrefix) (successor_rest))%I -∗
  instr_pre 0x800d6ae0 (∃ (successor_locals : DecodeItemReturnLocals), ZesuSsz.Contracts.RlpDecodeItemBlockEntries.decodeItemEntryAt800d6ae0 (args) (successor_locals))%I -∗
  decodeItemSelectedCode -∗
  instr_body 0x800d6960
    (DesignedEntry_800d6960 returnAddress args).
Proof.
iStartProof; ZesuSsz.Automation.Finish.zesu_expose_code_lists; repeat first [progress iIntros (?) | progress iIntros "#?" | progress iIntros "?"]; ZesuSsz.Automation.Finish.zesu_reduce_introduced_code_lists; repeat iDestruct select (_ ∗ _)%I as "[? ?]".
1: ltac2:(let rec run count := if Int.gt count 0 then (Control.focus 1 1 (fun () => ltac1:(tryif lazymatch goal with | |- envs_entails _ (@bi_exist _ _ _) => idtac | |- nat => idtac | |- list (bv 8) => idtac end then fail "HAND-WITNESS-FRONTIER" else zesu_liAStep)); run (Int.sub count 1)) else () in run 75).
1: iExists _.
1: multimatch goal with | |- context[Some ?chosen] => is_evar chosen; hand_witness_at_evar constr:(0%nat) chosen ltac:(unify chosen (Val_Bits (bv_and b 131072))) ltac:(iSplit; [done|]) end.
1: ltac2:(let rec run count := if Int.gt count 0 then (Control.focus 1 1 (fun () => ltac1:(tryif lazymatch goal with | |- envs_entails _ (@bi_exist _ _ _) => idtac | |- nat => idtac | |- list (bv 8) => idtac end then fail "HAND-WITNESS-FRONTIER" else zesu_liAStep)); run (Int.sub count 1)) else () in run 3).
1: iExists (Val_Bool (bool_decide (bv_and b 131072 = 0%bv))); iSplit; [done|].
1: ltac2:(let rec run count := if Int.gt count 0 then (Control.focus 1 1 (fun () => ltac1:(tryif lazymatch goal with | |- envs_entails _ (@bi_exist _ _ _) => idtac | |- nat => idtac | |- list (bv 8) => idtac end then fail "HAND-WITNESS-FRONTIER" else zesu_liAStep)); run (Int.sub count 1)) else () in run 38).
1: zesu_liAStep.
1: zesu_liAStep.
1: ltac2:(let rec run count := if Int.gt count 0 then (Control.focus 1 1 (fun () => ltac1:(first [lazymatch goal with | |- envs_entails _ (∃ x, "PC" ↦ᵣ _ ∗ _) => zesu_liAStep end | tryif lazymatch goal with | |- envs_entails _ (@bi_exist _ _ _) => idtac | |- nat => idtac | |- list (bv 8) => idtac end then fail "HAND-WITNESS-FRONTIER" else zesu_liAStep])); run (Int.sub count 1)) else () in run 55).
1: (iExists _; multimatch goal with | |- context[Some ?chosen] => is_evar chosen; hand_witness_at_evar constr:(0%nat) chosen ltac:(unify chosen (Val_Bits (bv_and b0 131072))) ltac:(iSplit; [done|]) end).
1: ltac2:(let rec run count := if Int.gt count 0 then (Control.focus 1 1 (fun () => ltac1:(first [lazymatch goal with | |- envs_entails _ (∃ x, "PC" ↦ᵣ _ ∗ _) => zesu_liAStep end | tryif lazymatch goal with | |- envs_entails _ (@bi_exist _ _ _) => idtac | |- nat => idtac | |- list (bv 8) => idtac end then fail "HAND-WITNESS-FRONTIER" else zesu_liAStep])); run (Int.sub count 1)) else () in run 3).
1: iExists (Val_Bool (bool_decide (bv_and b0 131072 = 0%bv))); iSplit; [done|].
1: ltac2:(let rec run count := if Int.gt count 0 then (Control.focus 1 1 (fun () => ltac1:(first [lazymatch goal with | |- envs_entails _ (∃ x, "PC" ↦ᵣ _ ∗ _) => zesu_liAStep end | tryif lazymatch goal with | |- envs_entails _ (@bi_exist _ _ _) => idtac | |- nat => idtac | |- list (bv 8) => idtac end then fail "HAND-WITNESS-FRONTIER" else zesu_liAStep])); run (Int.sub count 1)) else () in run 71).
1: iExists LET3; iSplit; [done|]; iIntros "%HstackStoreGuard".
1: ltac2:(let rec run count := if Int.gt count 0 then (Control.focus 1 1 (fun () => ltac1:(first [lazymatch goal with | |- envs_entails _ (∃ x, "PC" ↦ᵣ _ ∗ _) => zesu_liAStep end | tryif lazymatch goal with | |- envs_entails _ (@bi_exist _ _ _) => idtac | |- nat => idtac | |- list (bv 8) => idtac end then fail "HAND-WITNESS-FRONTIER" else zesu_liAStep])); run (Int.sub count 1)) else () in run 9).
1: iExists LET4; iSplit; [done|]; iIntros "%HstackStoreUpperGuard".
1: ltac2:(let rec run count := if Int.gt count 0 then (Control.focus 1 1 (fun () => ltac1:(first [lazymatch goal with | |- envs_entails _ (∃ x, "PC" ↦ᵣ _ ∗ _) => zesu_liAStep end | tryif lazymatch goal with | |- envs_entails _ (@bi_exist _ _ _) => idtac | |- nat => idtac | |- list (bv 8) => idtac end then fail "HAND-WITNESS-FRONTIER" else zesu_liAStep])); run (Int.sub count 1)) else () in run 75).
1: (iExists _; multimatch goal with | |- context[Some ?chosen] => is_evar chosen; hand_witness_at_evar constr:(0%nat) chosen ltac:(unify chosen (Val_Bits (bv_and b2 131072))) ltac:(iSplit; [done|]) end).
1: ltac2:(let rec run count := if Int.gt count 0 then (Control.focus 1 1 (fun () => ltac1:(first [lazymatch goal with | |- envs_entails _ (∃ x, "PC" ↦ᵣ _ ∗ _) => zesu_liAStep end | tryif lazymatch goal with | |- envs_entails _ (@bi_exist _ _ _) => idtac | |- nat => idtac | |- list (bv 8) => idtac end then fail "HAND-WITNESS-FRONTIER" else zesu_liAStep])); run (Int.sub count 1)) else () in run 3).
1: iExists (Val_Bool (bool_decide (bv_and b2 131072 = 0%bv))); iSplit; [done|].
1: ltac2:(let rec run count := if Int.gt count 0 then (Control.focus 1 1 (fun () => ltac1:(first [lazymatch goal with | |- envs_entails _ (∃ x, "PC" ↦ᵣ _ ∗ _) => zesu_liAStep end | tryif lazymatch goal with | |- envs_entails _ (@bi_exist _ _ _) => idtac | |- nat => idtac | |- list (bv 8) => idtac end then fail "HAND-WITNESS-FRONTIER" else zesu_liAStep])); run (Int.sub count 1)) else () in run 71).
1: iExists LET5; iSplit; [done|]; iIntros "%HstackSecondStoreGuard".
1: ltac2:(let rec run count := if Int.gt count 0 then (Control.focus 1 1 (fun () => ltac1:(first [lazymatch goal with | |- envs_entails _ (∃ x, "PC" ↦ᵣ _ ∗ _) => zesu_liAStep end | tryif lazymatch goal with | |- envs_entails _ (@bi_exist _ _ _) => idtac | |- nat => idtac | |- list (bv 8) => idtac end then fail "HAND-WITNESS-FRONTIER" else zesu_liAStep])); run (Int.sub count 1)) else () in run 9).
1: iExists LET6; iSplit; [done|]; iIntros "%HstackSecondStoreUpperGuard".
1: ltac2:(let rec run count := if Int.gt count 0 then (Control.focus 1 1 (fun () => ltac1:(first [lazymatch goal with | |- envs_entails _ (∃ x, "PC" ↦ᵣ _ ∗ _) => zesu_liAStep end | tryif lazymatch goal with | |- envs_entails _ (@bi_exist _ _ _) => idtac | |- nat => idtac | |- list (bv 8) => idtac end then fail "HAND-WITNESS-FRONTIER" else zesu_liAStep])); run (Int.sub count 1)) else () in run 46).
1: (iExists _; multimatch goal with | |- context[Some ?chosen] => is_evar chosen; hand_witness_at_evar constr:(0%nat) chosen ltac:(unify chosen (Val_Bits (bv_and b4 131072))) ltac:(iSplit; [done|]) end).
1: ltac2:(let rec run count := if Int.gt count 0 then (Control.focus 1 1 (fun () => ltac1:(first [lazymatch goal with | |- envs_entails _ (∃ x, "PC" ↦ᵣ _ ∗ _) => zesu_liAStep end | tryif lazymatch goal with | |- envs_entails _ (@bi_exist _ _ _) => idtac | |- nat => idtac | |- list (bv 8) => idtac end then fail "HAND-WITNESS-FRONTIER" else zesu_liAStep])); run (Int.sub count 1)) else () in run 3).
1: iExists (Val_Bool (bool_decide (bv_and b4 131072 = 0%bv))); iSplit; [done|].
1: ltac2:(let rec run count := if Int.gt count 0 then (Control.focus 1 1 (fun () => ltac1:(first [lazymatch goal with | |- envs_entails _ (∃ x, "PC" ↦ᵣ _ ∗ _) => zesu_liAStep end | tryif lazymatch goal with | |- envs_entails _ (@bi_exist _ _ _) => idtac | |- nat => idtac | |- list (bv 8) => idtac end then fail "HAND-WITNESS-FRONTIER" else zesu_liAStep])); run (Int.sub count 1)) else () in run 83).
1: (iExists _; multimatch goal with | |- context[Some ?chosen] => is_evar chosen; hand_witness_at_evar constr:(0%nat) chosen ltac:(unify chosen (Val_Bits (bv_and b5 131072))) ltac:(iSplit; [done|]) end).
1: ltac2:(let rec run count := if Int.gt count 0 then (Control.focus 1 1 (fun () => ltac1:(first [lazymatch goal with | |- envs_entails _ (∃ x, "PC" ↦ᵣ _ ∗ _) => zesu_liAStep end | tryif lazymatch goal with | |- envs_entails _ (@bi_exist _ _ _) => idtac | |- nat => idtac | |- list (bv 8) => idtac end then fail "HAND-WITNESS-FRONTIER" else zesu_liAStep])); run (Int.sub count 1)) else () in run 3).
1: iExists (Val_Bool (bool_decide (bv_and b5 131072 = 0%bv))); iSplit; [done|].
1: ltac2:(let rec run count := if Int.gt count 0 then (Control.focus 1 1 (fun () => ltac1:(first [lazymatch goal with | |- envs_entails _ (∃ x, "PC" ↦ᵣ _ ∗ _) => zesu_liAStep end | tryif lazymatch goal with | |- envs_entails _ (@bi_exist _ _ _) => idtac | |- nat => idtac | |- list (bv 8) => idtac end then fail "HAND-WITNESS-FRONTIER" else zesu_liAStep])); run (Int.sub count 1)) else () in run 37).
1: iExists LET9; iSplit; [done|]; iIntros "%HemptyLengthWord"; unfold LET9 in HemptyLengthWord; apply (bool_decide_eq_true_1 (Z_to_bv 64 (decodeItemInputLength args) = 0%bv)) in HemptyLengthWord.
1: ltac2:(let rec run count := if Int.gt count 0 then (Control.focus 1 1 (fun () => ltac1:(first [lazymatch goal with | |- envs_entails _ (∃ x, "PC" ↦ᵣ _ ∗ _) => zesu_liAStep end | tryif lazymatch goal with | |- envs_entails _ (@bi_exist _ _ _) => idtac | |- nat => idtac | |- list (bv 8) => idtac end then fail "HAND-WITNESS-FRONTIER" else zesu_liAStep])); run (Int.sub count 1)) else () in run 12).
1: iExists LET12; iSplit; [done|]; iIntros "%HemptyTargetAligned".
1: ltac2:(let rec run count := if Int.gt count 0 then (Control.focus 1 1 (fun () => ltac1:(first [lazymatch goal with | |- envs_entails _ (∃ x, "PC" ↦ᵣ _ ∗ _) => zesu_liAStep end | tryif lazymatch goal with | |- envs_entails _ (@bi_exist _ _ _) => idtac | |- nat => idtac | |- list (bv 8) => idtac end then fail "HAND-WITNESS-FRONTIER" else zesu_liAStep])); run (Int.sub count 1)) else () in run 13).
1: iRename select ((decodeItemStackPointer args + -16 + 0) ↦ₘ decodeItemSavedFramePointer args)%I into "HsavedFP".
1: iRename select ((decodeItemStackPointer args + -16 + 8) ↦ₘ Z_to_bv 64 (decodeItemReturnAddress args))%I into "HsavedRA".
1: iRename select (instr_pre returnAddress _)%I into "Hcaller".
1: iPoseProof (@zesu_pure_fact_intro _ _ _ (decodeItemSavedFrameRejectedIntroduction returnAddress args H0 HemptyLengthWord) with "[HsavedFP HsavedRA Hcaller]") as "HframeIntro"; [unfold decodeItemBranchContinuationAt; iFrame|].
1: iDestruct "HframeIntro" as (frameBytes) "((Hframe & %HframeFacts & Hcaller & _) & %HrejectedFacts)".
1: iExists {| returnA1 := Z_to_bv 64 (decodeItemInputPointer args); returnA2 := Z_to_bv 64 (decodeItemInputLength args); returnA3 := a3; returnA4 := a4; returnA5 := a5; returnA6 := a6; returnStorage := decodeItemBeforeStorage args; returnFrame := frameBytes |}.
1: unfold decodeItemEntryAt800d6ae0, decodeItemReturnEntryCore; cbn [returnA1 returnA2 returnA3 returnA4 returnA5 returnA6 returnStorage returnFrame].
1: replace (Z_to_bv 64 (decodeItemStackPointer args)) with LET7 by (unfold LET7; clear - args; bv_solve).
1: replace (Z_to_bv 64 (decodeItemStackPointer args - RlpDecodeItem.decodeItemStackBytes)) with (Z_to_bv 64 (decodeItemStackPointer args) + 18446744073709551600)%bv by (unfold RlpDecodeItem.decodeItemStackBytes; clear - args; bv_solve).
1: replace (decodeItemStackPointer args - RlpDecodeItem.decodeItemStackBytes)%Z with (decodeItemStackPointer args + -16 + 0)%Z by (unfold RlpDecodeItem.decodeItemStackBytes; lia).
1: replace (LET7 + 18446744073709551600)%bv with (Z_to_bv 64 (decodeItemStackPointer args) + 18446744073709551600)%bv by (unfold LET7; clear - args; bv_solve).
1: iFrame "Hframe Hcaller"; iFrame; iPureIntro; tauto.
1: zesu_block.
1: zesu_liAStep.
1: ltac2:(let rec run count := if Int.gt count 0 then (Control.focus 1 1 (fun () => ltac1:(first [lazymatch goal with | |- envs_entails _ (∃ x, "PC" ↦ᵣ _ ∗ _) => zesu_liAStep end | tryif lazymatch goal with | |- envs_entails _ (@bi_exist _ _ _) => idtac | |- nat => idtac | |- list (bv 8) => idtac end then fail "HAND-WITNESS-FRONTIER" else zesu_liAStep])); run (Int.sub count 1)) else () in run 2).
1: iExists (negb LET9); iSplit; [done|]; iIntros "%HnonemptyLengthWord"; apply negb_true_iff in HnonemptyLengthWord; unfold LET9 in HnonemptyLengthWord; apply (bool_decide_eq_false_1 (Z_to_bv 64 (decodeItemInputLength args) = 0%bv)) in HnonemptyLengthWord.
1: ltac2:(let rec run count := if Int.gt count 0 then (Control.focus 1 1 (fun () => ltac1:(first [lazymatch goal with | |- envs_entails _ (∃ x, "PC" ↦ᵣ _ ∗ _) => zesu_liAStep end | tryif lazymatch goal with | |- envs_entails _ (@bi_exist _ _ _) => idtac | |- nat => idtac | |- list (bv 8) => idtac end then fail "HAND-WITNESS-FRONTIER" else zesu_liAStep])); run (Int.sub count 1)) else () in run 11).
1: iPoseProof (@zesu_pure_fact_intro _ _ _ (decodeItemSavedFrameReturnIntroduction returnAddress args H0)) as "Hintro"; iEval (unfold decodeItemBranchContinuationAt) in "Hintro"; iDestruct ("Hintro" with "[$]") as (frameBytes) "(Hframe & %HframeFacts & Hcaller & _)".
1: assert (HnonzeroLength : bv_unsigned (Z_to_bv 64 (decodeItemInputLength args)) <> 0) by (intro Hz; apply HnonemptyLengthWord; apply bv_eq; change (bv_unsigned (Z_to_bv 64 (decodeItemInputLength args)) = 0); exact Hz).
1: destruct (DecodeItemSemanticIntroduction.decodeItemDomainNonemptyInputHead returnAddress args H0 HnonzeroLength) as (inputPrefix & rest & HinputHead).
1: iExists frameBytes, inputPrefix, rest; unfold decodeItemEntryAt800d6974; iExists a3, a4, a5, a6; iSplit; [iPureIntro; split; assumption|]; unfold decodeItemBranchBase.
1: replace LET7 with (Z_to_bv 64 (decodeItemStackPointer args)) by (unfold LET7; clear - args; bv_solve).
1: replace (Z_to_bv 64 (decodeItemStackPointer args - RlpDecodeItem.decodeItemStackBytes)) with (Z_to_bv 64 (decodeItemStackPointer args) + 18446744073709551600)%bv by (unfold RlpDecodeItem.decodeItemStackBytes; clear - args; bv_solve).
1: replace (decodeItemStackPointer args - RlpDecodeItem.decodeItemStackBytes)%Z with (decodeItemStackPointer args + -16 + 0)%Z by (unfold RlpDecodeItem.decodeItemStackBytes; lia).
1: iFrame "Hframe Hcaller"; iFrame; iPureIntro; exact HframeFacts.
all: zesu_block.
Unshelve.
all: zesu_finish_v1.
Qed.
