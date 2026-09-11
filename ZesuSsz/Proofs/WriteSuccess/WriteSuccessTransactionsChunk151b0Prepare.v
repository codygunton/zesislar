Require Import ZesuSsz.Automation.All.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary1519c.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary151b4.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsChunk151acReturn.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsChunk151acSetup.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsChunk151b0Prepared.

Import ListNotations WriteSuccessTransactionsSpec.

Lemma write_success_transactions_151b0_prepare
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  writeSuccessTransactions151b0SetupSpec P -∗
  writeSuccessTransactions151b0PreparedSpec.
Proof.
  iStartProof. iIntros "Hsetup".
  iEval (unfold writeSuccessTransactions151b0SetupSpec) in "Hsetup".
  iDestruct "Hsetup" as
    "(%sp & %base & %transaction & %transactions & %processed & %remaining &
      %bytes & %prefix & %suffix & %tail & %Halign & %Hmin & %Hmax &
      Hmachine & Hmmio & Htrace & Houter & Hnext & _)".
  iEval (unfold writeSuccessTransactionsMachine151b0) in "Hmachine".
  iDestruct "Hmachine" as
    "(Hsys & Hother & H1 & H2 & H5 & H8 & H9 & H10 & H11 & H18 & H19 &
      H20 & H21 & H22 & H23 & H24 & H25 & H26 & H27 & Hscratch & _)".
  iEval (rewrite /reg_col; cbn) in "Hother".
  iDestruct "Hother" as
    "(H3 & H4 & H6 & H7 & H12 & H13 & H14 & H15 & H16 & H17 & H28 & H29 &
      H30 & H31 & _)".
  iEval (rewrite reg_mapsto_pred_eq /reg_mapsto_pred_def) in "H5".
  iDestruct "H5" as (v5) "(H5 & %Hv5)".
  destruct (valu_has_bits_shape v5 64 Hv5) as (b5 & ->).
  iDestruct "H12" as (v12) "(%Hv12 & H12)".
  iDestruct "H13" as (v13) "(%Hv13 & H13)".
  iDestruct "H14" as (v14) "(%Hv14 & H14)".
  iDestruct "H15" as (v15) "(%Hv15 & H15)".
  iDestruct "H16" as (v16) "(%Hv16 & H16)".
  iDestruct "H17" as (v17) "(%Hv17 & H17)".
  destruct (valu_has_bits_shape v12 64 Hv12) as (b12 & ->).
  destruct (valu_has_bits_shape v13 64 Hv13) as (b13 & ->).
  destruct (valu_has_bits_shape v14 64 Hv14) as (b14 & ->).
  destruct (valu_has_bits_shape v15 64 Hv15) as (b15 & ->).
  destruct (valu_has_bits_shape v16 64 Hv16) as (b16 & ->).
  destruct (valu_has_bits_shape v17 64 Hv17) as (b17 & ->).
  iEval (unfold writeSuccessTransactionsScratch1519c) in "Hscratch".
  iDestruct "Hscratch" as "(Hscratch & HscratchTail)".
  iDestruct (mem_mapsto_uninit_split 48 with "Hscratch")
    as "[Hstack HscratchRest]"; first lia.
  iAssert (((bv_unsigned sp - 48) ↦ₘ? 48 -∗
      writeSuccessTransactionsScratch1519c
        sp base transactions processed transaction))%I
    with "[HscratchRest HscratchTail]" as "HscratchFrame".
  { iIntros "Hreturned".
    iAssert ((bv_unsigned sp - 48) ↦ₘ? 152)%I
      with "[Hreturned HscratchRest]" as "Hscratch".
    { iApply (mem_mapsto_uninit_combine 48 with "Hreturned"); first lia.
      iExact "HscratchRest". }
    rewrite /writeSuccessTransactionsScratch1519c.
    iFrame "Hscratch HscratchTail". }
  iAssert (reg_col ((fun r => (KindReg r, BitsShape 64)) <$>
      ["x3"; "x4"]))%I with "[H3 H4]" as "H34".
  { rewrite /reg_col. cbn. iFrame. }
  iPoseProof (write_success_transactions_151ac_return_frame_intro P sp base
    transaction transactions processed remaining bytes prefix suffix tail with
    "Houter H34 HscratchFrame") as "HreturnFrame".
  iAssert (instr_pre 0x151b4
      (writeSuccessTransactions151acCallRet sp transaction remaining tail))%I
    with "[Hnext HreturnFrame]" as "Hreturn".
  { iApply (instr_pre_wand 0x151b4 0x151b4 false true with "Hnext");
      [done | reflexivity |].
    iIntros "Hpost".
    iApply (write_success_transactions_151ac_return_adapter P sp base transaction
      transactions processed remaining bytes prefix suffix tail with
      "Hpost HreturnFrame"). }
  iAssert (reg_col ((fun r => (KindReg r, BitsShape 64)) <$>
      ["x6"; "x7"; "x28"; "x29"; "x30"; "x31"]))%I
    with "[H6 H7 H28 H29 H30 H31]" as "Htmp".
  { rewrite /reg_col. cbn. iFrame. }
  have Hbounds : 0x20000000 <= bv_unsigned sp - 48 /\
      bv_unsigned sp < 0x40000000 by lia.
  iEval (unfold writeSuccessTransactionPhaseEvents) in "Htrace".
  iExists sp, b5, b12, b13, b14, b15, b16, b17, transaction, remaining, tail.
  iFrame "Hsys H1".
  rewrite /writeSuccessTransactions151b0CallFrame.
  iFrame.
  repeat iSplit; try iPureIntro; try assumption; try lia; try done.
Qed.
