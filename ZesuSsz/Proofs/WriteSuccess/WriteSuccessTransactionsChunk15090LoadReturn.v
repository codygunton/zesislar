From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsBoundary14f1c.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsBoundary15094.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsChunk15090LoadState.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsChunk15090LoadArray.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsChunk15090LoadRegisters.

Lemma write_success_transactions_chunk_15090_load_return
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma)
    (sp : bv 64) (base : Z)
    (transaction : WriteSuccessTransactionsSpec.writeSuccessTransaction)
    (transactions processed remaining :
      list WriteSuccessTransactionsSpec.writeSuccessTransaction)
    (bytes prefix suffix : list (bv 8)) (tail : spec) :
  writeSuccessTransactions15090LoadResult P sp base transaction transactions
    processed remaining bytes prefix suffix tail -∗
  writeSuccessTransactionsAt15094Spec P.
Proof.
  rewrite /writeSuccessTransactions15090LoadResult.
  iIntros "(Hmachine & Hprefix128 & Hword128 & Hsuffix136 & Hphase &
    Hfacts & _)".
  iEval (unfold writeSuccessTransactionsLoadFacts) in "Hfacts".
  iDestruct "Hfacts" as
    "(%Hlength & %Halign & %Hlower & %Hupper & %HspAlign & %HspLower &
      %HspUpper & _)".
  iPoseProof (write_success_transactions_chunk_15090_load_registers sp base
    transactions processed transaction with "Hmachine") as "Hmachine".
  iPoseProof (write_success_transactions_chunk_15090_load_array base
    (length processed) transaction with
    "Hprefix128 Hsuffix136 Hword128 []") as "Harray".
  { iPureIntro. exact Hlength. }
  rewrite /writeSuccessTransactionsAt15094Spec.
  iExists sp, base, transaction, transactions, processed, remaining,
    bytes, prefix, suffix, tail.
  iFrame "Hmachine Harray Hphase".
  rewrite /writeSuccessTransactionsLoadFacts.
  repeat iSplit; try iPureIntro; try assumption; try done.
Qed.
