Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessCallAbi.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessEncoderBooleanCall.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsPriorityFeeBooleanAbiTail.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsPriorityFeeBooleanRegisters.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsPriorityFeeNoneBoundary.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsSpec.

Lemma write_success_transactions_priority_fee_boolean_abi_finalize
    `{!islaG Sigma} `{!threadG}
    (transaction : WriteSuccessTransactionsSpec.writeSuccessTransaction)
    (remaining : list WriteSuccessTransactionsSpec.writeSuccessTransaction)
    (sp : bv 64) (tail : spec) :
  writeSuccessTransactionsPriorityFeeBooleanAbiRegisters transaction sp (BV 64 0x15148)
    (writeSuccessTransactionsPriorityFeeBooleanAbiTail
      sp transaction remaining tail) -∗
  zesuEncoderBooleanCallSpec.
Proof.
  iStartProof. iIntros "Habi".
  iEval (unfold zesuEncoderBooleanCallSpec, zesu_c_call).
  iExists sp, (BV 64 0x15148).
  iEval (unfold writeSuccessTransactionsPriorityFeeBooleanAbiRegisters)
    in "Habi".
  iDestruct "Habi" as "(Hsys & Htmp & Hrest)".
  iEval (rewrite reg_mapsto_pred_eq /reg_mapsto_pred_def) in "Hrest".
  iDestruct "Hrest" as (r10) "(H10 & Hrest)".
  iDestruct "Hrest" as (b10) "(%Hr10 & Hrest)".
  iDestruct "Hrest" as (r11) "(H11 & Hrest)".
  iDestruct "Hrest" as (b11) "(%Hr11 & Hrest)".
  iDestruct "Hrest" as (r12) "(H12 & Hrest)".
  iDestruct "Hrest" as (b12) "(%Hr12 & Hrest)".
  iDestruct "Hrest" as (r13) "(H13 & Hrest)".
  iDestruct "Hrest" as (b13) "(%Hr13 & Hrest)".
  iDestruct "Hrest" as (r14) "(H14 & Hrest)".
  iDestruct "Hrest" as (b14) "(%Hr14 & Hrest)".
  iDestruct "Hrest" as (r15) "(H15 & Hrest)".
  iDestruct "Hrest" as (b15) "(%Hr15 & Hrest)".
  iDestruct "Hrest" as (r16) "(H16 & Hrest)".
  iDestruct "Hrest" as (b16) "(%Hr16 & Hrest)".
  iDestruct "Hrest" as (r17) "(H17 & Hrest)".
  iDestruct "Hrest" as (b17) "(%Hr17 & Hrest)".
  iDestruct "Hrest" as "(Hsaved & H1 & H2 & HR)".
  iEval (rewrite /writeSuccessTransactionsPriorityFeeSavedShapes /reg_col /=)
    in "Hsaved".
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
  iEval (rewrite reg_mapsto_pred_eq /reg_mapsto_pred_def).
  iFrame "Hsys Htmp H10 H11 H12 H13 H14 H15 H16 H17 H1 H2".
  iExists b10. iSplit; first done.
  iExists b11. iSplit; first done.
  iExists b12. iSplit; first done.
  iExists b13. iSplit; first done.
  iExists b14. iSplit; first done.
  iExists b15. iSplit; first done.
  iExists b16. iSplit; first done.
  iExists b17. iSplit; first done.
  iExists (RVal_Bits (writeSuccessTransactionWord transaction 192)).
  iFrame "H8". iSplit; first done.
  iExists (RVal_Bits (writeSuccessTransactionWord transaction 16)).
  iFrame "H9". iSplit; first done.
  iExists (RVal_Bits (writeSuccessTransactionWord transaction 48)).
  iFrame "H18". iSplit; first done.
  iExists (RVal_Bits (writeSuccessTransactionWord transaction 224)).
  iFrame "H19". iSplit; first done.
  iExists (RVal_Bits (writeSuccessTransactionWord transaction 56)).
  iFrame "H20". iSplit; first done.
  iExists (RVal_Bits (writeSuccessTransactionWord transaction 72)).
  iFrame "H21". iSplit; first done.
  iExists (RVal_Bits (writeSuccessTransactionWord transaction 200)).
  iFrame "H22". iSplit; first done.
  iExists (RVal_Bits (writeSuccessTransactionWord transaction 24)).
  iFrame "H23". iSplit; first done.
  iExists (RVal_Bits (writeSuccessTransactionWord transaction 8)).
  iFrame "H24". iSplit; first done.
  iExists (RVal_Bits (writeSuccessTransactionWord transaction 0)).
  iFrame "H25". iSplit; first done.
  iExists (RVal_Bits (writeSuccessTransactionWord transaction 184)).
  iFrame "H26". iSplit; first done.
  iExists (RVal_Bits (bv_zero_extend 64
    (writeSuccessTransactionByte transaction 32))).
  iFrame "H27". iSplit; first done.
  iEval (unfold writeSuccessTransactionsPriorityFeeBooleanAbiTail) in "HR".
  iExact "HR".
Qed.
