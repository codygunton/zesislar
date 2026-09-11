Require Import ZesuSsz.Automation.All.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import
  Index HintsTransactionsLoop.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessBitvector.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessEncoderBooleanCall.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessEncoderInt1645Call.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary15118.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary15148.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsChunk15118Branch.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsPriorityFeeSome.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsPriorityFeeNone.

Local Remove Hints subsume_instr_pre'_inst : typeclass_instances.
Local Existing Instance subsume_instr_pre_wand_inst | 1.

Lemma write_success_transactions_chunk_15118
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  □ instr_pre 0x15b9c zesuEncoderBooleanCallSpec -∗
  □ instr_pre 0x15ce4 zesuEncoderInt1645CallSpec -∗
  instr_body 0x15148 (writeSuccessTransactionsAt15148Spec P) -∗
  instr_body 0x15118 (writeSuccessTransactionsAt15118Spec P).
Proof.
  iStartProof.
  iIntros "#Hlookup #Hcode #Hboolean #Hint Hnext".
  iPoseProof (write_success_transactions_priority_fee_none P with
    "Hlookup Hcode Hboolean") as "HnoneK".
  iPoseProof (write_success_transactions_priority_fee_some P with
    "Hlookup Hcode Hboolean Hint") as "HsomeK".
  iPoseProof "Hlookup" as "#Hlookup15118".
  iEval (rewrite /instr_lookup_resources) in "Hlookup15118".
  iPoseProof ("Hlookup15118" $! 0x15118 with "[]") as "#Hinstr15118".
  { iPureIntro. rewrite IslaTraces.write_success_blocks.Index.lookup_a15118.
    done. }
  rewrite instr_pre'_eq.
  iIntros "Hentry".
  iEval (unfold writeSuccessTransactionsAt15118Spec) in "Hentry".
  iDestruct "Hentry" as
    "(%sp & %base & %transaction & %transactions & %processed & %remaining &
      %bytes & %prefix & %suffix & %tail & Hphase)".
  destruct (decide
    (writeSuccessTransactionByte transaction 32 = BV 8 0)) as [Hzero|Hnonzero].
  - iSpecialize ("HnoneK" with "Hnext").
    iRename "HnoneK" into "Hbody".
    iAssert (instr_pre 0x1513c
        (writeSuccessTransactionsPriorityFeeNoneAt1513cSpec P))%I
      with "[Hbody]" as "HnextBranch".
    { iApply instr_pre_to_body. iNext.
      rewrite instr_pre'_eq. iExact "Hbody". }
    iEval (unfold writeSuccessTransactionPhaseHandoff) in "Hphase".
    iDestruct "Hphase" as "(Hmachine & HphaseTail)".
    iEval (unfold writeSuccessTransactionsMachine15118) in "Hmachine".
    iDestruct "Hmachine" as
      "(Hsys & Hother & H1 & H2 & H5 & H8 & H9 & H10 & H11 & H18 & H19 &
        H20 & H21 & H22 & H23 & H24 & H25 & H26 & H27 & Hscratch & _)".
    iPoseProof (instr_pre_wand 0x1513c 0x1513c true true
      (writeSuccessTransactionsPriorityFeeNoneAt1513cSpec P)
      (writeSuccessTransactions15118BranchState True%I
        (bv_zero_extend 64 (writeSuccessTransactionByte transaction 32)))
      with "HnextBranch")
      as "HnextRaw"; [done | done | idtac].
    iSpecialize ("HnextRaw" with
      "[Hother H1 H2 H5 H8 H9 H10 H11 H18 H19 H20 H21 H22 H23 H24 H25 H26 Hscratch HphaseTail]").
    { rewrite /writeSuccessTransactions15118BranchState.
      iIntros "(Hsys & H27 & _)".
      iExists sp, base, transaction, transactions, processed, remaining,
        bytes, prefix, suffix, tail.
      iSplit; first (iPureIntro; exact Hzero).
      rewrite /writeSuccessTransactionPhaseHandoff.
      iSplitL "Hsys Hother H1 H2 H5 H8 H9 H10 H11 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 Hscratch".
      { rewrite /writeSuccessTransactionsMachine15118. iFrame. }
      iExact "HphaseTail". }
    have HdataZero :
      bv_zero_extend 64 (writeSuccessTransactionByte transaction 32) = BV 64 0.
    { rewrite Hzero. bv_solve. }
    iPoseProof (write_success_transactions_15118_zero_branch True%I
      (bv_zero_extend 64 (writeSuccessTransactionByte transaction 32))
      HdataZero with "Hinstr15118 HnextRaw") as "Hraw".
    iEval (rewrite instr_pre'_eq) in "Hraw".
    iApply "Hraw".
    rewrite /writeSuccessTransactions15118BranchState. iFrame.
  - iSpecialize ("HsomeK" with "Hnext").
    iRename "HsomeK" into "Hbody".
    iAssert (instr_pre 0x1511c
        (writeSuccessTransactionsPriorityFeeSomeAt1511cSpec P))%I
      with "[Hbody]" as "HnextBranch".
    { iApply instr_pre_to_body. iNext.
      rewrite instr_pre'_eq. iExact "Hbody". }
    iEval (unfold writeSuccessTransactionPhaseHandoff) in "Hphase".
    iDestruct "Hphase" as "(Hmachine & HphaseTail)".
    iEval (unfold writeSuccessTransactionsMachine15118) in "Hmachine".
    iDestruct "Hmachine" as
      "(Hsys & Hother & H1 & H2 & H5 & H8 & H9 & H10 & H11 & H18 & H19 &
        H20 & H21 & H22 & H23 & H24 & H25 & H26 & H27 & Hscratch & _)".
    iPoseProof (instr_pre_wand 0x1511c 0x1511c true true
      (writeSuccessTransactionsPriorityFeeSomeAt1511cSpec P)
      (writeSuccessTransactions15118BranchState True%I
        (bv_zero_extend 64 (writeSuccessTransactionByte transaction 32)))
      with "HnextBranch")
      as "HnextRaw"; [done | done | idtac].
    iSpecialize ("HnextRaw" with
      "[Hother H1 H2 H5 H8 H9 H10 H11 H18 H19 H20 H21 H22 H23 H24 H25 H26 Hscratch HphaseTail]").
    { rewrite /writeSuccessTransactions15118BranchState.
      iIntros "(Hsys & H27 & _)".
      iExists sp, base, transaction, transactions, processed, remaining,
        bytes, prefix, suffix, tail.
      iSplit; first (iPureIntro; exact Hnonzero).
      rewrite /writeSuccessTransactionPhaseHandoff.
      iSplitL "Hsys Hother H1 H2 H5 H8 H9 H10 H11 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 Hscratch".
      { rewrite /writeSuccessTransactionsMachine15118. iFrame. }
      iExact "HphaseTail". }
    have HdataNonzero :
      bv_zero_extend 64 (writeSuccessTransactionByte transaction 32) ≠ BV 64 0.
    { intros HzeroExtend. apply Hnonzero.
      exact (bv_zero_extend_64_zero_8 _ HzeroExtend). }
    iPoseProof (write_success_transactions_15118_nonzero_branch True%I
      (bv_zero_extend 64 (writeSuccessTransactionByte transaction 32))
      HdataNonzero with "Hinstr15118 HnextRaw") as "Hraw".
    iEval (rewrite instr_pre'_eq) in "Hraw".
    iApply "Hraw".
    rewrite /writeSuccessTransactions15118BranchState. iFrame.
Qed.
