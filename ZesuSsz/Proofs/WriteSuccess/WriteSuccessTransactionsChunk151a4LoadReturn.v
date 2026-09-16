Require Import ZesuSsz.Automation.AllLegacy.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary151a8.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsChunk151a4LoadState.

Lemma write_success_transactions_151a4_load_return
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma)
    (sp : bv 64) (base : Z)
    (transaction : WriteSuccessTransactionsSpec.writeSuccessTransaction)
    (transactions processed remaining :
      list WriteSuccessTransactionsSpec.writeSuccessTransaction)
    (bytes prefix suffix : list (bv 8)) (tail : spec) :
  writeSuccessTransactions151a4LoadResult P sp base transaction transactions
    processed remaining bytes prefix suffix tail -∗
  writeSuccessTransactionsAt151a8Spec P.
Proof.
  rewrite /writeSuccessTransactions151a4LoadResult.
  iIntros "(Hmachine & Houter & %Halign & %Hmin & %Hmax & _)".
  iEval (unfold writeSuccessTransactions151a4Outer,
    WriteSuccessTransactionsSpec.writeSuccessTransactionPhaseHandoff) in
    "Houter".
  iDestruct "Houter" as
    "(_ & HbasePrefix & HbaseSuffix & Hprocessed & Htransaction & Hremaining &
      Hmmio & Htrace & HP & Hinvariant & Hexit & _)".
  rewrite /writeSuccessTransactionsAt151a8Spec.
  iExists sp, base, transaction, transactions, processed, remaining,
    bytes, prefix, suffix, tail.
  iSplit; first by iPureIntro.
  iSplit; first by iPureIntro.
  iSplit; first by iPureIntro.
  rewrite /writeSuccessTransactions151a4Outer
    /WriteSuccessTransactionsSpec.writeSuccessTransactionPhaseHandoff.
  iFrame "Hmachine HbasePrefix HbaseSuffix Hprocessed Htransaction Hremaining
    Hmmio Htrace HP Hinvariant Hexit".
Qed.
