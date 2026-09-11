Require Import ZesuSsz.Automation.All.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessAccessListsSpec.

Definition writeSuccessAccessListsAt15200Spec `{!islaG Sigma} `{!threadG}
    (x19 : bv 64) (P : iProp Sigma) : iProp Sigma :=
  writeSuccessAccessListsCopiedSpec AccessListsOutput x19 P.

Global Instance : LithiumUnfold (@writeSuccessAccessListsAt15200Spec) := I.
