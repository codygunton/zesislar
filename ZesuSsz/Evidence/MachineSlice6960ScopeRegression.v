Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith NArith.NArith.
Require Import stdpp.bitvector.definitions.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Open Scope Z_scope.

Definition machineScopeRegression `{!islaG Sigma} `{!threadG}
  (p : Z) (bytes : list (bv 8%N)) (K : iProp Sigma) : iProp Sigma :=
  (K ∗
  ⌜(p + (-16) = p - 16)%Z⌝ ∗
  ⌜(List.length bytes = 40)%nat⌝ ∗
  True)%I.
