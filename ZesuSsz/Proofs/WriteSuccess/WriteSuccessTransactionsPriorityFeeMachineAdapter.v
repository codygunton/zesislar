Require Import ZesuSsz.Automation.AllLegacy.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary150e8.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary15118.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsPriorityFeeNoneBoundary.

Import ListNotations.

Definition writeSuccessTransactionsPriorityFeeMachineParts
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma)
    (sp : bv 64) (base : Z) (transaction : writeSuccessTransaction)
    (transactions processed remaining : list writeSuccessTransaction)
    (bytes prefix suffix : list (bv 8)) (tail : spec) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗
   reg_col ((fun r => (KindReg r, BitsShape 64)) <$> tmp_registers) ∗
   reg_col writeSuccessTransactionsPriorityFeeCallerShapes ∗
   reg_col (writeSuccessTransactionsPriorityFeeSavedShapes transaction) ∗
   "x1" ↦ᵣ RVal_Bits (BV 64 0x15118) ∗ "x2" ↦ᵣ RVal_Bits sp ∗
   "x10" ↦ᵣ RVal_Bits (sp - BV 64 32)%bv ∗
   "x11" ↦ᵣ RVal_Bits (BV 64 16) ∗
   (bv_unsigned sp - 16) ↦ₘ? 16 ∗
   writeSuccessTransactionsPriorityFeeMachineCallerFrame P sp base transaction
     transactions processed remaining bytes prefix suffix tail ∗ True)%I.

Global Instance : LithiumUnfold
  (@writeSuccessTransactionsPriorityFeeMachineParts) := I.

Lemma write_success_transactions_priority_fee_machine_split
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma)
    (sp : bv 64) (base : Z) (transaction : writeSuccessTransaction)
    (transactions processed remaining : list writeSuccessTransaction)
    (bytes prefix suffix : list (bv 8)) (tail : spec) :
  writeSuccessTransactionsMachine15118
    sp base transactions processed transaction -∗
  writeSuccessTransactionsPriorityFeeMachineParts P sp base transaction
    transactions processed remaining bytes prefix suffix tail.
Proof.
  iIntros "Hmachine".
  iEval (unfold writeSuccessTransactionsMachine15118) in "Hmachine".
  iDestruct "Hmachine" as
    "(Hsys & Hother & H1 & H2 & H5 & H8 & H9 & H10 & H11 & H18 & H19 &
      H20 & H21 & H22 & H23 & H24 & H25 & H26 & H27 & Hscratch & _)".
  iEval (rewrite !reg_col_cons reg_col_nil) in "Hother".
  iDestruct "Hother" as
    "(H3 & H4 & H6 & H7 & H12 & H13 & H14 & H15 & H16 & H17 &
      H28 & H29 & H30 & H31 & _)".
  iEval (unfold writeSuccessTransactionsScratch150e8) in "Hscratch".
  iDestruct "Hscratch" as "(HscratchPrefix & HscratchTail)".
  iDestruct (mem_mapsto_uninit_split 32 with "HscratchPrefix") as
    "[HscratchLow HscratchHigh]"; first lia.
  have HcallAddress : bv_unsigned sp - 48 + 32 = bv_unsigned sp - 16 by lia.
  iEval (rewrite HcallAddress) in "HscratchHigh".
  iDestruct (mem_mapsto_uninit_split 16 with "HscratchHigh") as
    "[HcallStack HscratchUpper]"; first lia.
  have HupperAddress : bv_unsigned sp - 16 + 16 = bv_unsigned sp by lia.
  iEval (rewrite HupperAddress) in "HscratchUpper".
  iAssert (((bv_unsigned sp - 16) ↦ₘ? 16 -∗
      writeSuccessTransactionsScratch150e8
        sp base transactions processed transaction))%I
    with "[HscratchLow HscratchUpper HscratchTail]" as "HscratchRestore".
  { iIntros "HreturnedStack".
    iEval (unfold writeSuccessTransactionsScratch150e8).
    iAssert ((bv_unsigned sp - 48) ↦ₘ? 48)%I
      with "[HscratchLow HreturnedStack]" as "HscratchLow48".
    { iApply (mem_mapsto_uninit_combine 32 with "HscratchLow"); first lia.
      rewrite HcallAddress. iExact "HreturnedStack". }
    iAssert ((bv_unsigned sp - 48) ↦ₘ? 152)%I
      with "[HscratchLow48 HscratchUpper]" as "HscratchPrefix".
    { iApply (mem_mapsto_uninit_combine 48 with "HscratchLow48"); first lia.
      have -> : bv_unsigned sp - 48 + 48 = bv_unsigned sp by lia.
      iExact "HscratchUpper". }
    iFrame. }
  iEval (unfold writeSuccessTransactionsPriorityFeeMachineParts).
  iAssert (reg_col ((fun r => (KindReg r, BitsShape 64)) <$> tmp_registers))
    with "[H5 H6 H7 H28 H29 H30 H31]" as "Htmp".
  { rewrite /tmp_registers !reg_col_cons reg_col_nil. iFrame.
    repeat iSplit; iPureIntro; done. }
  iAssert (reg_col writeSuccessTransactionsPriorityFeeCallerShapes)
    with "[H12 H13 H14 H15 H16 H17]" as "Hcaller".
  { rewrite /writeSuccessTransactionsPriorityFeeCallerShapes
      !reg_col_cons reg_col_nil. iFrame; done. }
  iAssert (reg_col (writeSuccessTransactionsPriorityFeeSavedShapes transaction))
    with "[H8 H9 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27]" as "Hsaved".
  { rewrite /writeSuccessTransactionsPriorityFeeSavedShapes
      !reg_col_cons reg_col_nil. iFrame; done. }
  iAssert (writeSuccessTransactionsPriorityFeeMachineCallerFrame P sp base
      transaction transactions processed remaining bytes prefix suffix tail)
    with "[H3 H4 HscratchRestore]" as "HmachineFrame".
  { iEval (unfold writeSuccessTransactionsPriorityFeeMachineCallerFrame).
    rewrite !reg_col_cons reg_col_nil. iFrame; done. }
  iFrame.
Qed.
