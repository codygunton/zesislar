From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessAccessListsSpec.

Definition writeSuccessAccessListsAt15210Spec `{!islaG Sigma} `{!threadG}
    (x19 : bv 64) (P : iProp Sigma) : iProp Sigma :=
  writeSuccessAccessListsCopiedSpec AccessListsCount x19 P.

Global Instance : LithiumUnfold (@writeSuccessAccessListsAt15210Spec) := I.
