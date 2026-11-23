Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.TxAccessListSelected.
Require Import ZesuSsz.Contracts.TxAccessListContract.

(* Function-specific unfolding markers. These declarations add no generic rule. *)
Global Typeclasses Opaque txAccessListSelectedCode.
Global Instance : LithiumUnfold (@txAccessListSelectedCode) := I.
Global Typeclasses Opaque txAccessListContractCode.
Global Instance : LithiumUnfold (@txAccessListContractCode) := I.
Global Typeclasses Opaque txOwnedSlice.
Global Instance : LithiumUnfold (@txOwnedSlice) := I.
Global Typeclasses Opaque txAccessListReturnedHeap.
Global Instance : LithiumUnfold (@txAccessListReturnedHeap) := I.
Global Typeclasses Opaque txAccessListEntryResources.
Global Instance : LithiumUnfold (@txAccessListEntryResources) := I.
Global Typeclasses Opaque txAccessListExitResources.
Global Instance : LithiumUnfold (@txAccessListExitResources) := I.
