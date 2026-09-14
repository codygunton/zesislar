Require Import ZesuSsz.Automation.All.
Require Import ZesuMachineMap.Machine.
From Coq Require Import Lists.List.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessCallAbi.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary150f0.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary15148.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsPriorityFeeCore.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsPriorityFeeNoneBoundary.

Import ListNotations.

Definition writeSuccessTransactionsPriorityFeeSavedValues
    (transaction : writeSuccessTransaction) : list valu :=
  [RVal_Bits (writeSuccessTransactionWord transaction 192);
   RVal_Bits (writeSuccessTransactionWord transaction 16);
   RVal_Bits (writeSuccessTransactionWord transaction 48);
   RVal_Bits (writeSuccessTransactionWord transaction 224);
   RVal_Bits (writeSuccessTransactionWord transaction 56);
   RVal_Bits (writeSuccessTransactionWord transaction 72);
   RVal_Bits (writeSuccessTransactionWord transaction 200);
   RVal_Bits (writeSuccessTransactionWord transaction 24);
   RVal_Bits (writeSuccessTransactionWord transaction 8);
   RVal_Bits (writeSuccessTransactionWord transaction 0);
   RVal_Bits (writeSuccessTransactionWord transaction 184);
   RVal_Bits (bv_zero_extend 64 (writeSuccessTransactionByte transaction 32))].

Lemma write_success_transactions_priority_fee_boolean_return
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma)
    (sp : bv 64) (base : Z) (transaction : writeSuccessTransaction)
    (transactions processed remaining : list writeSuccessTransaction)
    (bytes prefix suffix : list (bv 8)) (tail : spec) :
  zesu_c_call_ret 16
    (writeSuccessTransactionsPriorityFeeSavedValues transaction)
    (BV 64 0x15148) sp
    (fun _ =>
      mmio_range (machineOutputAddress defaultMap) 16 ∗
      spec_trace
        (writeSuccessTransactionPhaseEvents TransactionGasLimit sp transaction
          (writeSuccessTransactionsEvents sp remaining tail)) ∗
      writeSuccessTransactionsPriorityFeeCallerFrame P sp base transaction
        transactions processed remaining bytes prefix suffix tail ∗ True) -∗
  writeSuccessTransactionsPriorityFeePostSpec P.
Proof.
  iIntros "Hret".
  iEval (unfold zesu_c_call_ret) in "Hret".
  iDestruct "Hret" as "(Hsys & Htmp & Hsaved & Hrest)".
  iEval (rewrite reg_mapsto_pred_eq /reg_mapsto_pred_def) in "Hrest".
  iDestruct "Hrest" as (r10) "(H10 & Hrest)".
  iDestruct "Hrest" as (b10) "(%Hr10Bits & Hrest)".
  iDestruct "Hrest" as (r11) "(H11 & Hrest)".
  iDestruct "Hrest" as (b11) "(%Hr11Bits & H2 & Hstack & HQ)".
  subst r10 r11.
  iDestruct "HQ" as "(Hmmio & Htrace & Hcaller & _)".
  iEval (unfold writeSuccessTransactionsPriorityFeeCallerFrame) in "Hcaller".
  iDestruct "Hcaller" as "(HmachineCaller & Hframe & _)".
  iEval (unfold writeSuccessTransactionsPriorityFeeMachineCallerFrame) in
    "HmachineCaller".
  iDestruct "HmachineCaller" as "(H34 & HscratchRestore & _)".
  iSpecialize ("HscratchRestore" with "Hstack").
  iEval (rewrite /reg_col /=) in "Htmp Hsaved H34".
  iDestruct "Htmp" as
    "(H1 & H12 & H13 & H14 & H15 & H16 & H17 & H5 & H6 & H7 & H28 & H29 &
      H30 & H31 & _)".
  iDestruct "Hsaved" as
    "(H8 & H9 & H18 & H19 & H20 & H21 & H22 & H23 & H24 & H25 & H26 &
      H27 & _)".
  iDestruct "H8" as (v8) "(%Hv8 & H8)". subst v8.
  iDestruct "H9" as (v9) "(%Hv9 & H9)". subst v9.
  iDestruct "H18" as (v18) "(%Hv18 & H18)". subst v18.
  iDestruct "H19" as (v19) "(%Hv19 & H19)". subst v19.
  iDestruct "H20" as (v20) "(%Hv20 & H20)". subst v20.
  iDestruct "H21" as (v21) "(%Hv21 & H21)". subst v21.
  iDestruct "H22" as (v22) "(%Hv22 & H22)". subst v22.
  iDestruct "H23" as (v23) "(%Hv23 & H23)". subst v23.
  iDestruct "H24" as (v24) "(%Hv24 & H24)". subst v24.
  iDestruct "H25" as (v25) "(%Hv25 & H25)". subst v25.
  iDestruct "H26" as (v26) "(%Hv26 & H26)". subst v26.
  iDestruct "H27" as (v27) "(%Hv27 & H27)". subst v27.
  iDestruct "H34" as "(H3 & H4 & _)".
  iExists sp, base, transaction, transactions, processed, remaining,
    bytes, prefix, suffix, tail.
  rewrite /writeSuccessTransactionsMachine15148
    /writeSuccessTransactionsMachine150f0.
  iFrame "Hsys H2 H8 H9 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27
    HscratchRestore Hmmio Htrace Hframe".
  rewrite /writeSuccessTransactions150f0OtherRegShapes /reg_col /=.
  iFrame "H1 H3 H4 H5 H6 H7 H10 H11 H12 H13 H14 H15 H16 H17 H28 H29 H30
    H31".
  repeat iSplit; try iPureIntro; try reflexivity; try assumption; try done.
Qed.
