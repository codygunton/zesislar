Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessNativeCode WriteSuccessTransactionsSpec
  WriteSuccessExactTransactionsSpec WriteSuccessExactTransactionsLiveSpec
  WriteSuccessExactTransactionsLoopIndexEntry
  WriteSuccessExactTransactionsLiveZeroBlobBridge
  WriteSuccessExactTransactionsLiveFieldRegion.

Lemma transactions_live_zero_field_to_loop `{!islaG Sigma} `{!threadG}
    sp base transactions processed transaction rest bytes tail (P : iProp Sigma) :
  transactionLoopSourceFacts sp base transactions processed (transaction :: rest) bytes ->
  Forall writeSuccessTransactionValid processed ->
  writeSuccessTransactionValid transaction ->
  writeSuccessCompleteNativeCode -∗
  □ instr_pre 0x153d0
    (transactionLiveCurrentFieldEntry sp base transactions processed transaction rest bytes tail P) -∗
  instr_body 0x14f08
    (transactionLiveLoopState sp base transactions processed (transaction :: rest) bytes tail P).
Proof.
  intros Hfacts Hprocessed Hvalid. iIntros "#Hcode #Hfield".
  iEval (rewrite instr_pre'_eq). iIntros "Hstate".
  iPoseProof (transactions_live_current_field_region sp base transactions processed
    transaction rest bytes tail P Hfacts Hprocessed Hvalid with "Hcode Hfield") as "Hregion".
  iEval (rewrite instr_pre'_eq) in "Hregion".
  iApply "Hregion".
  iApply (transactions_loop_to_index with "Hstate").
Qed.
Print Assumptions transactions_live_zero_field_to_loop.
