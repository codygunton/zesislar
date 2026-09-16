Require Import ZesuSsz.Automation.AllLegacy.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary14f1c.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary15088.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsChunk15088LoadSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsChunk15088LoadState.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsChunk15088LoadFrame.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsChunk15088LoadArrayPrepare.

Lemma write_success_transactions_chunk_15088_load_prepare
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma)
    (sp : bv 64) (base : Z)
    (transaction : WriteSuccessTransactionsSpec.writeSuccessTransaction)
    (transactions processed remaining :
      list WriteSuccessTransactionsSpec.writeSuccessTransaction)
    (bytes prefix suffix : list (bv 8)) (tail : spec) :
  writeSuccessTransactionsAt15088Block P sp base transaction transactions
    processed remaining bytes prefix suffix tail -∗
  writeSuccessTransactions15088LoadState P sp base transaction transactions
    processed remaining bytes prefix suffix tail.
Proof.
  rewrite /writeSuccessTransactionsAt15088Block
    /writeSuccessTransactionsMachine15088.
  iIntros "(Hmachine & Harray & Hphase & Hfacts & %Hcurrent & _)".
  iEval (unfold writeSuccessTransactionsLoadFacts) in "Hfacts".
  iDestruct "Hfacts" as
    "(%Hlength & %Halign & %Hlower & %Hupper & %HspAlign & %HspLower &
      %HspUpper & _)".
  iPoseProof (write_success_transactions_chunk_15088_load_frame sp base
    transactions processed transaction _ with "Hmachine") as
    "(Hsys & Hx15 & Hx10 & HmachineFrame)".
  iPoseProof (write_success_transactions_chunk_15088_load_array_prepare base
    (length processed) transaction with "[] Harray") as
    "(Hprefix120 & Hword120 & Hsuffix128)".
  { iPureIntro. exact Hlength. }
  rewrite /writeSuccessTransactions15088LoadState.
  iFrame "Hsys Hx15 Hx10 Hprefix120 Hword120 Hsuffix128 HmachineFrame
    Hphase".
  rewrite /writeSuccessTransactionsLoadFacts.
  repeat iSplit; try iPureIntro; try assumption; try done.
Qed.
