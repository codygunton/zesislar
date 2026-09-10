From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessCallAbi.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessCalls.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary150e8.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactions10190MachineAdapter.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary10190Prepared.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactions10190ReturnBuilder.

Lemma write_success_transactions_10190_prepared_to_call
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma)
    (sp : bv 64) (base : Z) (transaction : writeSuccessTransaction)
    (transactions processed remaining : list writeSuccessTransaction)
    (bytes prefix suffix : list (bv 8)) (tail : spec) :
  writeSuccessTransactionsAt10190PreparedBlock P sp base transaction
    transactions processed remaining bytes prefix suffix tail -∗
  zesuWriteOutputCallSpec.
Proof.
  iIntros "Hentry".
  iPoseProof (write_success_transactions_10190_prepared_unpack P sp base
    transaction transactions processed remaining bytes prefix suffix tail with
    "Hentry") as
    "(Hmachine & %HspAlign & %HspMin & %HspMax & Hmmio & Htrace &
      Hreturn & _)".
  iPoseProof (write_success_transactions_10190_machine_frame_unpack sp base
    transaction transactions processed with "Hmachine") as
    "(Hsys & H1 & Hmachine & _)".
  iEval (unfold writeSuccessTransactionsMachine150e8Rest) in "Hmachine".
  iDestruct "Hmachine" as
    "(Hother & H2 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 &
      H14 & H15 & H16 & H17 & H18 & H19 & H20 & H21 & H22 & H23 & H24 &
      H25 & H26 & H27 & H28 & H29 & H30 & H31 & Hscratch & _)".
  iAssert (writeSuccessTransactions10190MachineFrame
      sp base transaction transactions processed)
    with "[Hother Hscratch]" as "HreturnMachine".
  { rewrite /writeSuccessTransactions10190MachineFrame. iFrame. }
  iPoseProof (write_success_transactions_10190_return_builder_apply sp base
    transaction transactions processed remaining tail with
    "Hreturn HreturnMachine") as "Hreturn".
  rewrite /zesuWriteOutputCallSpec /zesu_c_call.
  iExists sp, (BV 64 0x150f0).
  rewrite /tmp_registers !reg_col_cons reg_col_nil.
  iEval (rewrite !reg_mapsto_pred_eq /reg_mapsto_pred_def).
  iFrame.
  repeat (iSplit; first (iPureIntro; cbn; done)).
  iExists (writeSuccessTransactionWord transaction 248).
  iSplit; first done.
  iExists (writeSuccessTransactionWord transaction 273).
  iSplit; first done.
  iExists (bv_or
      (bv_or
        (bv_shiftl
          (bv_zero_extend 64 (writeSuccessTransactionByte transaction 284))
          (BV 64 24))
        (bv_shiftl
          (bv_zero_extend 64 (writeSuccessTransactionByte transaction 283))
          (BV 64 16)))
      (bv_or
        (bv_shiftl
          (bv_zero_extend 64 (writeSuccessTransactionByte transaction 282))
          (BV 64 8))
        (bv_zero_extend 64 (writeSuccessTransactionByte transaction 281)))).
  iSplit; first done.
  iExists (writeSuccessTransactionWord transaction 128).
  iSplit; first done.
  iExists
    (bv_shiftl
      (bv_or
        (bv_or
          (bv_shiftl
            (bv_zero_extend 64 (writeSuccessTransactionByte transaction 272))
            (BV 64 24))
          (bv_shiftl
            (bv_zero_extend 64 (writeSuccessTransactionByte transaction 271))
            (BV 64 16)))
        (bv_or
          (bv_shiftl
            (bv_zero_extend 64 (writeSuccessTransactionByte transaction 270))
            (BV 64 8))
          (bv_zero_extend 64 (writeSuccessTransactionByte transaction 269))))
      (BV 64 32)).
  iSplit; first done.
  iExists (bv_or
      (bv_shiftl
        (bv_zero_extend 64 (writeSuccessTransactionByte transaction 276))
        (BV 64 24))
      (bv_shiftl
        (bv_zero_extend 64 (writeSuccessTransactionByte transaction 275))
        (BV 64 16))).
  iSplit; first done.
  repeat iSplit; try iPureIntro; try assumption; try bv_solve; try lia;
    try iFrame.
  all: try (cbn; done).
  Unshelve.
  all: try prepare_sidecond.
  all: try assumption.
  all: try bv_solve.
  all: try lia.
  all: try iFrame.
  all: try (cbn; done).
  all: try (rewrite mem_mapsto_uninit_0; iPureIntro; bv_solve).
  Unshelve.
  all: try (rewrite mem_mapsto_uninit_0; iPureIntro; bv_solve).
Qed.
