Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.NextUint64BlockEntries.
Require Import ZesuSsz.Contracts.NextUint64Contract.
Require Import ZesuSsz.Contracts.NextUint64Selected.

(* Function-specific unfolding markers. These declarations add no generic rule. *)
Global Typeclasses Opaque nextUint64Registers.
Global Instance : LithiumUnfold (@nextUint64Registers) := I.
Global Typeclasses Opaque nextUint64PostMemory.
Global Instance : LithiumUnfold (@nextUint64PostMemory) := I.
Global Typeclasses Opaque nextUint64EntryAt800d6274.
Global Instance : LithiumUnfold (@nextUint64EntryAt800d6274) := I.
Global Typeclasses Opaque nextUint64EntryAt800d62b8.
Global Instance : LithiumUnfold (@nextUint64EntryAt800d62b8) := I.
Global Typeclasses Opaque nextUint64EntryAt800d62c0.
Global Instance : LithiumUnfold (@nextUint64EntryAt800d62c0) := I.
Global Typeclasses Opaque nextUint64EntryAt800d62cc.
Global Instance : LithiumUnfold (@nextUint64EntryAt800d62cc) := I.
Global Typeclasses Opaque nextUint64EntryAt800d62d8.
Global Instance : LithiumUnfold (@nextUint64EntryAt800d62d8) := I.
Global Typeclasses Opaque nextUint64EntryAt800d62e4.
Global Instance : LithiumUnfold (@nextUint64EntryAt800d62e4) := I.
Global Typeclasses Opaque nextUint64EntryAt800d6304.
Global Instance : LithiumUnfold (@nextUint64EntryAt800d6304) := I.
Global Typeclasses Opaque nextUint64EntryAt800d6310.
Global Instance : LithiumUnfold (@nextUint64EntryAt800d6310) := I.
Global Typeclasses Opaque nextUint64EntryAt800d6318.
Global Instance : LithiumUnfold (@nextUint64EntryAt800d6318) := I.
Global Typeclasses Opaque nextUint64EntryAt800d632c.
Global Instance : LithiumUnfold (@nextUint64EntryAt800d632c) := I.
Global Typeclasses Opaque nextUint64BoundaryEntry.
Global Instance : LithiumUnfold (@nextUint64BoundaryEntry) := I.
Global Typeclasses Opaque nextUint64ContractEntry.
Global Instance : LithiumUnfold (@nextUint64ContractEntry) := I.
Global Typeclasses Opaque nextUint64ContractExit.
Global Instance : LithiumUnfold (@nextUint64ContractExit) := I.

Global Typeclasses Opaque nextUint64SelectedCode.
Global Instance nextUint64SelectedCodeUnfold : LithiumUnfold (@nextUint64SelectedCode) := I.
Global Typeclasses Opaque nextUint64SelectedEntry.
Global Instance nextUint64SelectedEntryUnfold : LithiumUnfold (@nextUint64SelectedEntry) := I.
Global Typeclasses Opaque nextUint64SelectedExit.
Global Instance nextUint64SelectedExitUnfold : LithiumUnfold (@nextUint64SelectedExit) := I.
