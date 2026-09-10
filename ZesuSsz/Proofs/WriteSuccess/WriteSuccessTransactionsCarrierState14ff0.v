Require Import ZesuSsz.Automation.All.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsCarrierState14fe4.

Definition writeSuccessTransactionsAt14ff0CarrierSpec
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
      (bv_zero_extend 64
        (WriteSuccessTransactionsSpec.writeSuccessTransactionByte
          transaction 270))
      (bv_zero_extend 64
        (WriteSuccessTransactionsSpec.writeSuccessTransactionByte
          transaction 271)))%I.

Global Instance : LithiumUnfold
    (@writeSuccessTransactionsAt14ff0CarrierSpec) := I.
