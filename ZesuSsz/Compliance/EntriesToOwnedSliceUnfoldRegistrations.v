Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.EntriesToOwnedSliceBlockEntries.

(* entriesToOwnedSlice unfolding markers for the block-entry interface. These declarations add no generic rule. *)
Global Typeclasses Opaque entriesBlockEntryResources.
Global Instance : LithiumUnfold (@entriesBlockEntryResources) := I.
Global Typeclasses Opaque entriesBlockExitResources.
Global Instance : LithiumUnfold (@entriesBlockExitResources) := I.
