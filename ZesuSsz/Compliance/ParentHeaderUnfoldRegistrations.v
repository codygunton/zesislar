Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.ParentHeaderContract.

(* Measurement-only unfolding markers for the decodeParentHeader entry interface.
   These declarations add no generic rule. *)
Global Typeclasses Opaque parentHeaderEntryResources.
Global Instance : LithiumUnfold (@parentHeaderEntryResources) := I.
Global Typeclasses Opaque parentHeaderExitRegisterResources.
Global Instance : LithiumUnfold (@parentHeaderExitRegisterResources) := I.
Global Typeclasses Opaque parentHeaderExitResources.
Global Instance : LithiumUnfold (@parentHeaderExitResources) := I.
