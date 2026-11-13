Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.ParentHeaderContract.
Require Import ZesuSsz.Contracts.ParentHeaderMemcpyService.

(* Function-specific unfolding markers. These declarations add no generic rule. *)
Global Typeclasses Opaque parentHeaderSelectedCode.
Global Instance : LithiumUnfold (@parentHeaderSelectedCode) := I.
Global Typeclasses Opaque parentHeaderContractCode.
Global Instance : LithiumUnfold (@parentHeaderContractCode) := I.
Global Typeclasses Opaque parentHeaderEntryResources.
Global Instance : LithiumUnfold (@parentHeaderEntryResources) := I.
Global Typeclasses Opaque parentHeaderExitResources.
Global Instance : LithiumUnfold (@parentHeaderExitResources) := I.
Global Typeclasses Opaque memcpyCallPremise.
Global Instance : LithiumUnfold (@memcpyCallPremise) := I.
