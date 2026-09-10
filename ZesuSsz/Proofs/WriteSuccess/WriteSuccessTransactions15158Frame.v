From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsBoundary15158.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsChunk15154Frame.

Lemma write_success_transactions_15158_pack
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) (sp : bv 64) (base : Z)
    (transaction : WriteSuccessTransactionsSpec.writeSuccessTransaction)
    (transactions processed remaining :
      list WriteSuccessTransactionsSpec.writeSuccessTransaction)
    (bytes prefix suffix : list (bv 8)) (tail : spec) :
  writeSuccessTransactionsMachine15158 sp base transactions processed transaction -∗
  writeSuccessTransactions15168Frame P sp base transaction transactions processed
    remaining bytes prefix suffix tail -∗
  writeSuccessTransactionsAt15158Spec P.
Proof.
  iIntros "Hmachine Hframe".
  iExists sp, base, transaction, transactions, processed, remaining, bytes, prefix,
    suffix, tail.
  iEval (unfold WriteSuccessTransactionsSpec.writeSuccessTransactionPhaseHandoff).
  iFrame.
Qed.
