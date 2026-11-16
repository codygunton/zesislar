Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.BerlinGasCalcContract.

(* W0 held-out unfolding markers for the entry interface. These declarations add no generic rule. *)
Global Typeclasses Opaque berlinGasCalcEntryResources.
Global Instance : LithiumUnfold (@berlinGasCalcEntryResources) := I.
Global Typeclasses Opaque berlinGasCalcExitResources.
Global Instance : LithiumUnfold (@berlinGasCalcExitResources) := I.
