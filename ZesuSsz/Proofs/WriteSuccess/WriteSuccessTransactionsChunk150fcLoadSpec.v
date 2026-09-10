From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary150fc.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary15100.

Definition writeSuccessTransactions150fcLoadEntry
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma)
    (sp : bv 64) (base : Z) (transaction : writeSuccessTransaction)
    (transactions processed remaining : list writeSuccessTransaction)
    (bytes prefix suffix : list (bv 8)) (tail : spec) : iProp Sigma :=
  writeSuccessTransactionPhaseHandoff TransactionNonce
    (writeSuccessTransactionsMachine150fc
      sp base transactions processed transaction)
    sp base transaction transactions processed remaining
    bytes prefix suffix tail P.

Definition writeSuccessTransactions15100LoadPost
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma)
    (sp : bv 64) (base : Z) (transaction : writeSuccessTransaction)
    (transactions processed remaining : list writeSuccessTransaction)
    (bytes prefix suffix : list (bv 8)) (tail : spec) : iProp Sigma :=
  writeSuccessTransactionPhaseHandoff TransactionNonce
    (writeSuccessTransactionsMachine15100
      sp base transactions processed transaction)
    sp base transaction transactions processed remaining
    bytes prefix suffix tail P.

Global Instance : LithiumUnfold (@writeSuccessTransactions150fcLoadEntry) := I.
Global Instance : LithiumUnfold (@writeSuccessTransactions15100LoadPost) := I.
