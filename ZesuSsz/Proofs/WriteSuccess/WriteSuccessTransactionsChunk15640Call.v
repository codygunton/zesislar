From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import Index HintsTransactionsLoop.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessCallAbi.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessEncoderU256.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary15640.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary15644.

Local Remove Hints subsume_instr_pre'_inst : typeclass_instances.
Local Existing Instance subsume_instr_pre_wand_inst | 1.

Lemma write_success_transactions_chunk_15640_call
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  □ instr_pre 0x15cb0 zesuEncoderU256CallSpec -∗
  instr_body 0x15644 (writeSuccessTransactionsAt15644Spec P) -∗
  instr_body 0x15640 (writeSuccessTransactionsAt15640Spec P).
Proof.
  move => *.
  iStartProof.
  iIntros "_ #Hlookup #Hcode #Hu256 Hnext".
  iAssert (□ (True -∗ instr_pre 0x15cb0 zesuEncoderU256CallSpec))%I
    with "[]" as "#Hu256Hidden".
  { iModIntro. iIntros "_". iExact "Hu256". }
  iClear "Hu256".
  iEval (unfold IslaTraces.write_success_blocks.Index.spec_instr_resources)
    in "Hcode".
  do 65 liAStep.
  rewrite /Specs.zesu_jalr_same_spec.
  iExists (BV 64 0x1563c).
  iFrame.
  iSplit; first (iPureIntro; bv_solve).
  have Htarget :
    bv_unsigned
      (bv_or (bv_and ((BV 64 0x1563c) + BV 64 1652)%bv
        (BV 64 18446744073709551614)) (BV 64 0)) = 0x15cb0
    by native_compute.
  rewrite Htarget.
  iSpecialize ("Hu256Hidden" with "[]"). { done. }
  iApply (instr_pre_wand 0x15cb0 0x15cb0 true true with "Hu256Hidden");
    [done | reflexivity |].
  iIntros "Hentry".
  iEval (unfold zesuEncoderU256CallSpec, zesu_c_call).
  iExists sp, (BV 64 0x15644).
  iDestruct "Hentry" as "(Hsys & H1 & _)".
  iFrame.
  liARun.
  iExists
    (tail, suffix, prefix, bytes, remaining, processed, transactions,
      transaction, base, sp, tt)ₗ.
  iDestruct select
    (writeSuccessTransactions15640Frame sp base transaction transactions
      processed remaining bytes prefix suffix tail P) as "Hframe".
  iEval (unfold writeSuccessTransactions15640Frame) in "Hframe".
  iDestruct "Hframe" as
    "(Hfixed & Hscratch & Hprefix & Hsuffix & Hprocessed & Htransaction &
     Hremaining & HP & Hinvariant & Hexit & _)".
  iFrame "Hscratch Hprefix Hsuffix Htransaction Hremaining HP
    Hinvariant Hexit".
  iEval (unfold WriteSuccessTransactionsSpec.writeSuccessTransactionsProcessedOwn).
  liARun.
  all: try iFrame.
  Unshelve. all: prepare_sidecond.
  all: try assumption.
  all: try bv_solve.
  all: try lia.
Qed.
