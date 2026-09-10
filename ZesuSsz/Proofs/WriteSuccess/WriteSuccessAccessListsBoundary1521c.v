From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Experiments.WriteSuccessAccessListsSpec.

Definition writeSuccessAccessListsAt1521cSpec `{!islaG Sigma} `{!threadG}
    (x19 : bv 64) (P : iProp Sigma) : iProp Sigma :=
  writeSuccessAccessListsCopiedSpec AccessListsStorage x19 P.

Global Instance : LithiumUnfold (@writeSuccessAccessListsAt1521cSpec) := I.
