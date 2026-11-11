Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.ResumeCallContract.

(* W0 held-out unfolding markers for the entry interface. These declarations add no generic rule. *)
Global Typeclasses Opaque resumeCallEntryResources.
Global Instance : LithiumUnfold (@resumeCallEntryResources) := I.
Global Typeclasses Opaque resumeCallExitRegisterResources.
Global Instance : LithiumUnfold (@resumeCallExitRegisterResources) := I.
Global Typeclasses Opaque resumeCallExitResources.
Global Instance : LithiumUnfold (@resumeCallExitResources) := I.
