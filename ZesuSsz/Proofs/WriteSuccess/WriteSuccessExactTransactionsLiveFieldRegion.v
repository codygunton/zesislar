Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessNativeCode WriteSuccessTransactionsSpec
  WriteSuccessExactTransactionsSpec WriteSuccessExactTransactionsLiveSpec
  WriteSuccessExactTransactionsLoopIndexEntry
  WriteSuccessExactTransactionsIndexCell
  WriteSuccessExactTransactionsIndexSourceEntry
  WriteSuccessExactTransactionsTypeTailModel
  WriteSuccessExactTransactionsLiveSourceRegion
  WriteSuccessExactTransactionsLiveZeroBlobBridge.
Lemma transactions_live_current_field_region `{!islaG Sigma} `{!threadG}
    sp base transactions processed transaction rest bytes tail (P : iProp Sigma) :
  transactionLoopSourceFacts sp base transactions processed (transaction :: rest) bytes ->
  Forall writeSuccessTransactionValid processed ->
  writeSuccessTransactionValid transaction ->
  writeSuccessCompleteNativeCode -∗
  □ instr_pre 0x153d0
    (transactionLiveCurrentFieldEntry sp base transactions processed transaction rest bytes tail P) -∗
  instr_body 0x14f08 (transactionIndexCellEntry sp (Z_to_bv 64 base)
    (Z_to_bv 64 (Z.of_nat (length processed)))
    (Z_to_bv 64 (Z.of_nat (length transactions)))
    (transactionIndexSourceCaller sp base bytes (length processed)
      (writeSuccessExactTransactionAfterTypeEvents sp transaction
        (writeSuccessExactTransactionsEvents sp rest tail))
      (transactionLoopSourceFrame sp base transactions processed (transaction :: rest) bytes P))).
Proof.
  intros Hfacts Hprocessed Hvalid. iIntros "#Hcode #Hfield".
  iEval (unfold transactionLiveCurrentFieldEntry) in "Hfield".
  iApply (transactions_live_source_region_correct sp base transactions processed
    transaction rest bytes tail P Hfacts Hprocessed Hvalid with "Hcode Hfield").
Qed.
Print Assumptions transactions_live_current_field_region.
