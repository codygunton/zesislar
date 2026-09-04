From Coq Require Import Lists.List.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Experiments.WriteSuccessCallAbi.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsChunk150f0Spec.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsBoundary150f0.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsBoundary150fc.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsChunk150f8ScratchRest.

Import ListNotations.

Lemma write_success_transactions_150fc_raw_return_adapter
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma)
    (sp : bv 64) (base : Z)
    (transaction : WriteSuccessTransactionsSpec.writeSuccessTransaction)
    (transactions processed remaining :
      list WriteSuccessTransactionsSpec.writeSuccessTransaction)
    (bytes prefix suffix : list (bv 8)) (tail : spec)
    (tagTail : list (bv 8)) :
  zesu_c_call_ret 32
    [RVal_Bits (WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 192);
     RVal_Bits (WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 16);
     RVal_Bits (WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 48);
     RVal_Bits (WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 224);
     RVal_Bits (WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 56);
     RVal_Bits (WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 72);
     RVal_Bits (WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 200);
     RVal_Bits (WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 24);
     RVal_Bits (WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 8);
     RVal_Bits (WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 0);
     RVal_Bits (WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 184);
     RVal_Bits (bv_zero_extend 64
       (WriteSuccessTransactionsSpec.writeSuccessTransactionByte transaction 32))]
    (BV 64 0x150fc) sp
    (fun _ =>
      reg_col ([(KindReg "x3", BitsShape 64); (KindReg "x4", BitsShape 64)]) ∗
      writeSuccessTransactions150f0Frame P sp base transaction transactions
        processed remaining bytes prefix suffix tail ∗
      writeSuccessTransactionsScratchRest150f8 sp base transactions processed transaction ∗
      (bv_unsigned sp + 1664) ↦ₘ
        WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 160 ∗
      (bv_unsigned sp + 1672) ↦ₘ BV 8 0 ∗
      (bv_unsigned sp + 1673) ↦ₘ∗ tagTail ∗
      mmio_range 0x2401a0c0 16 ∗
      spec_trace
        (WriteSuccessTransactionsSpec.writeSuccessTransactionPhaseEvents
          WriteSuccessTransactionsSpec.TransactionNonce sp transaction
          (WriteSuccessTransactionsSpec.writeSuccessTransactionsEvents
            sp remaining tail)) ∗ True) -∗
  ⌜bv_to_little_endian 8 8
      (bv_unsigned
        (WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 168)) =
      BV 8 0 :: tagTail⌝ -∗
  writeSuccessTransactionsAt150fcFramedSpec P.
Proof.
  iIntros "Hret" (Hshape).
  iEval (unfold zesu_c_call_ret) in "Hret".
  iDestruct "Hret" as "(Hsys & Htmp & Hsaved & Hrest)".
  iEval (rewrite reg_mapsto_pred_eq /reg_mapsto_pred_def) in "Hrest".
  iDestruct "Hrest" as (r10) "(H10 & Hrest)".
  iDestruct "Hrest" as (b10) "(%Hr10Bits & Hrest)".
  iDestruct "Hrest" as (r11) "(H11 & Hrest)".
  iDestruct "Hrest" as (b11) "(%Hr11Bits & H2 & Hstack & HQ)".
  subst r10 r11.
  iDestruct "HQ" as
    "(Hcaller34 & Hframe & HscratchRest & Hvalue & Htag & Htail & Hmmio & Htrace & _)".
  iEval (rewrite /reg_col /=) in "Htmp Hsaved".
  iDestruct "Htmp" as
    "(H1 & H12 & H13 & H14 & H15 & H16 & H17 & H5 & H6 & H7 & H28 & H29 &
      H30 & H31 & _)".
  iEval (rewrite /reg_col /=) in "Hcaller34".
  iDestruct "Hcaller34" as "(H3 & H4 & _)".
  iDestruct "Hsaved" as
    "(H8 & H9 & H18 & H19 & H20 & H21 & H22 & H23 & H24 & H25 & H26 & H27 & _)".
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
  iPoseProof (write_success_transactions_scratch_150f8_combine
    sp base transactions processed transaction tagTail
    with "HscratchRest Hvalue Htag Htail") as "Hscratch".
  iSpecialize ("Hscratch" with "[]").
  { iPureIntro. exact Hshape. }
  iExists sp, base, transaction, transactions, processed, remaining,
    bytes, prefix, suffix, tail.
  rewrite /writeSuccessTransactionsMachine150fc
    /writeSuccessTransactionsMachine150f0.
  iFrame "Hsys H2 H8 H9 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27
    Hscratch Hmmio Htrace Hframe".
  rewrite /writeSuccessTransactions150f0OtherRegShapes /reg_col /=.
  iFrame "H1 H3 H4 H5 H6 H7 H10 H11 H12 H13 H14 H15 H16 H17 H28 H29 H30 H31".
  iFrame.
  repeat iSplit; try iPureIntro; try reflexivity; try assumption; try done.
  Unshelve. all: try prepare_sidecond; try bv_solve; try lia; try iFrame.
Qed.
