From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsBoundary15090.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsBoundary15094.

Lemma write_success_transactions_chunk_15090_load_registers
    `{!islaG Sigma} `{!threadG} (sp : bv 64) (base : Z)
    (transactions processed :
      list WriteSuccessTransactionsSpec.writeSuccessTransaction)
    (transaction : WriteSuccessTransactionsSpec.writeSuccessTransaction) :
  writeSuccessTransactionsMachine15090WithX15 sp base transactions processed
    transaction
    (RVal_Bits
      (WriteSuccessTransactionsSpec.writeSuccessTransactionWord
        transaction 128)) -∗
  writeSuccessTransactionsMachine15094
    sp base transactions processed transaction.
Proof.
  rewrite /writeSuccessTransactionsMachine15090WithX15
    /writeSuccessTransactionsMachine15094.
  iIntros "Hmachine".
  iExact "Hmachine".
Qed.
