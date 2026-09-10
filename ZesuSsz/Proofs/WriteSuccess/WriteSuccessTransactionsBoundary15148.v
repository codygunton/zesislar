From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary150f0.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary15118.

Definition writeSuccessTransactionsMachine15148 `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (base : Z) (transactions processed :
      list writeSuccessTransaction) (transaction : writeSuccessTransaction) :
    iProp Sigma :=
  writeSuccessTransactionsMachine150f0
    sp base transactions processed transaction.

Global Instance : LithiumUnfold (@writeSuccessTransactionsMachine15148) := I.

Definition writeSuccessTransactionsPriorityFeeSomeAt1511cSpec
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) : iProp Sigma :=
  (∃ (sp : bv 64) (base : Z) (transaction : writeSuccessTransaction)
      (transactions processed remaining : list writeSuccessTransaction)
      (bytes prefix suffix : list (bv 8)) (tail : spec),
    ⌜writeSuccessTransactionByte transaction 32 ≠ BV 8 0⌝ ∗
    writeSuccessTransactionPhaseHandoff TransactionGasPriorityFee
      (writeSuccessTransactionsMachine15118
        sp base transactions processed transaction)
      sp base transaction transactions processed remaining
      bytes prefix suffix tail P)%I.

Global Instance :
  LithiumUnfold (@writeSuccessTransactionsPriorityFeeSomeAt1511cSpec) := I.

Definition writeSuccessTransactionsPriorityFeeNoneAt1513cSpec
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) : iProp Sigma :=
  (∃ (sp : bv 64) (base : Z) (transaction : writeSuccessTransaction)
      (transactions processed remaining : list writeSuccessTransaction)
      (bytes prefix suffix : list (bv 8)) (tail : spec),
    ⌜writeSuccessTransactionByte transaction 32 = BV 8 0⌝ ∗
    writeSuccessTransactionPhaseHandoff TransactionGasPriorityFee
      (writeSuccessTransactionsMachine15118
        sp base transactions processed transaction)
      sp base transaction transactions processed remaining
      bytes prefix suffix tail P)%I.

Global Instance :
  LithiumUnfold (@writeSuccessTransactionsPriorityFeeNoneAt1513cSpec) := I.

Definition writeSuccessTransactionsAt15148Spec `{!islaG Sigma} `{!threadG}
    (P : iProp Sigma) : iProp Sigma :=
  (∃ (sp : bv 64) (base : Z) (transaction : writeSuccessTransaction)
      (transactions processed remaining : list writeSuccessTransaction)
      (bytes prefix suffix : list (bv 8)) (tail : spec),
    writeSuccessTransactionPhaseHandoff TransactionGasLimit
      (writeSuccessTransactionsMachine15148
        sp base transactions processed transaction)
      sp base transaction transactions processed remaining
      bytes prefix suffix tail P)%I.

Global Instance : LithiumUnfold (@writeSuccessTransactionsAt15148Spec) := I.
