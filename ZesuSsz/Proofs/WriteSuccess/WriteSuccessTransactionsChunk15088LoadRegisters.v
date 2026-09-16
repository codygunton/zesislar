Require Import ZesuSsz.Automation.AllLegacy.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary15088.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary1508c.

Lemma write_success_transactions_chunk_15088_load_registers
    `{!islaG Sigma} `{!threadG} (sp : bv 64) (base : Z)
    (transactions processed :
      list WriteSuccessTransactionsSpec.writeSuccessTransaction)
    (transaction : WriteSuccessTransactionsSpec.writeSuccessTransaction) :
  writeSuccessTransactionsMachine15088WithX15 sp base transactions processed
    transaction
    (RVal_Bits
      (WriteSuccessTransactionsSpec.writeSuccessTransactionWord
        transaction 120)) -∗
  writeSuccessTransactionsMachine1508c
    sp base transactions processed transaction.
Proof.
  rewrite /writeSuccessTransactionsMachine15088WithX15
    /writeSuccessTransactionsMachine1508c.
  iIntros "Hmachine".
  iExact "Hmachine".
Qed.
