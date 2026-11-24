Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.KeysEnsureCapacityBlockEntries.

(* keysEnsureCapacity unfolding markers for the block-entry interface. These declarations add no generic rule. *)
Global Typeclasses Opaque ensureBlockEntryResources.
Global Instance : LithiumUnfold (@ensureBlockEntryResources) := I.
Global Typeclasses Opaque ensureBlockExitResources.
Global Instance : LithiumUnfold (@ensureBlockExitResources) := I.
