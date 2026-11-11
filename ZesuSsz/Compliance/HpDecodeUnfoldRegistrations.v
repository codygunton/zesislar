Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.HpDecodeContract.

(* W0 held-out unfolding markers for the entry interface. These declarations add no generic rule. *)
Global Typeclasses Opaque hpDecodeEntryResources.
Global Instance : LithiumUnfold (@hpDecodeEntryResources) := I.
Global Typeclasses Opaque hpDecodeExitRegisterResources.
Global Instance : LithiumUnfold (@hpDecodeExitRegisterResources) := I.
Global Typeclasses Opaque hpDecodeExitResources.
Global Instance : LithiumUnfold (@hpDecodeExitResources) := I.
