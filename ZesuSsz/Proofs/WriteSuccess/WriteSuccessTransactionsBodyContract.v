From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundarySpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary1519c.

Definition writeSuccessTransactionsBodyPrefixContract
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) : iProp Sigma :=
  □ (instr_body 0x1519c (writeSuccessTransactionsAt1519cSpec P) -∗
     instr_body 0x14f08 (writeSuccessTransactionsAt14f08Spec P)).

Global Instance : LithiumUnfold
    (@writeSuccessTransactionsBodyPrefixContract) := I.
