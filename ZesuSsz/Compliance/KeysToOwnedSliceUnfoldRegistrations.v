Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.KeysToOwnedSliceBlockEntries.

(* keysToOwnedSlice unfolding markers for the block-entry interface. These declarations add no generic rule. *)
Global Typeclasses Opaque keysBlockEntryResources.
Global Instance : LithiumUnfold (@keysBlockEntryResources) := I.
Global Typeclasses Opaque keysBlockExitResources.
Global Instance : LithiumUnfold (@keysBlockExitResources) := I.
