Require Import ZesuSsz.Automation.AllLegacy.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary14f1c.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary1508c.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsChunk15088LoadState.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsChunk15088LoadArray.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsChunk15088LoadRegisters.

Lemma write_success_transactions_chunk_15088_load_return
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma)
    (sp : bv 64) (base : Z)
    (transaction : WriteSuccessTransactionsSpec.writeSuccessTransaction)
    (transactions processed remaining :
      list WriteSuccessTransactionsSpec.writeSuccessTransaction)
    (bytes prefix suffix : list (bv 8)) (tail : spec) :
  writeSuccessTransactions15088LoadResult P sp base transaction transactions
    processed remaining bytes prefix suffix tail -∗
  writeSuccessTransactionsAt1508cSpec P.
Proof.
  rewrite /writeSuccessTransactions15088LoadResult.
  iIntros "(Hmachine & Hprefix120 & Hword120 & Hsuffix128 & Hphase &
    Hfacts & _)".
  iEval (unfold writeSuccessTransactionsLoadFacts) in "Hfacts".
  iDestruct "Hfacts" as
    "(%Hlength & %Halign & %Hlower & %Hupper & %HspAlign & %HspLower &
      %HspUpper & _)".
  iPoseProof (write_success_transactions_chunk_15088_load_registers sp base
    transactions processed transaction with "Hmachine") as "Hmachine".
  iPoseProof (write_success_transactions_chunk_15088_load_array base
    (length processed) transaction with
    "Hprefix120 Hsuffix128 Hword120 []") as "Harray".
  { iPureIntro. exact Hlength. }
  rewrite /writeSuccessTransactionsAt1508cSpec.
  iExists sp, base, transaction, transactions, processed, remaining,
    bytes, prefix, suffix, tail.
  iFrame "Hmachine Harray Hphase".
  rewrite /writeSuccessTransactionsLoadFacts.
  repeat iSplit; try iPureIntro; try assumption; try done.
Qed.
