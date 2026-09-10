Require Import ZesuSsz.Automation.All.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsCarrierState14fe4.

Definition writeSuccessTransactionsAt14fe8CarrierSpec
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) : iProp Sigma :=
  (∃ transaction first second third fourth items,
    writeSuccessTransactionsAt14fe0CarrierLoadSpec P
      transaction first second third fourth items
      (bv_zero_extend 64
        (WriteSuccessTransactionsSpec.writeSuccessTransactionByte
          transaction 268))
      (bv_zero_extend 64
        (WriteSuccessTransactionsSpec.writeSuccessTransactionByte
          transaction 269))
      (bv_shiftl
        (bv_zero_extend 64
          (WriteSuccessTransactionsSpec.writeSuccessTransactionByte
            transaction 276))
        (BV 64 24))
      (bv_zero_extend 64
        (WriteSuccessTransactionsSpec.writeSuccessTransactionByte
          transaction 277)))%I.

Global Instance : LithiumUnfold
    (@writeSuccessTransactionsAt14fe8CarrierSpec) := I.
