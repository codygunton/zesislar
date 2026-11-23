Require Import ZesuSsz.Generated.KeysToOwnedSlice.FP301.Pilot01d8Entries.
Require Import ZesuSsz.Generated.KeysToOwnedSlice.FP301.Pilot01d8Structural.
Require Import ZesuSsz.Generated.KeysToOwnedSlice.FP301.Pilot018cEntries.
Require Import ZesuSsz.Generated.KeysToOwnedSlice.FP301.Pilot018cStructural.
Require Import ZesuSsz.Generated.KeysToOwnedSlice.FP301.Pilot01e0Entries.
Require Import ZesuSsz.Generated.KeysToOwnedSlice.FP301.Pilot01e0Structural.
Require Import ZesuSsz.Automation2.All.
Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith NArith.NArith.
Require Import stdpp.bitvector.definitions.
Require Import ZesuSsz.Contracts.KeysToOwnedSliceBlockEntries.
Require Import ZesuSsz.Contracts.KeysToOwnedSliceSelected.
Require Import ZesuSsz.Automation2.All.
Local Open Scope Z_scope.
#[local] Typeclasses Transparent keysToOwnedSliceSelectedCode.

Definition DesignedEntry_800d6954
    `{!islaG Sigma} `{!threadG} (args : KeysToOwnedSliceBlockArgs) (returnAddress : Z) (K : iProp Sigma) : iProp Sigma :=
  ((ZesuSsz.Generated.KeysToOwnedSlice.FP301.Pilot01d8Entries.fp_machineAt01d8 (args) (returnAddress) (K)) ∗
   True)%I.
Global Instance : LithiumUnfold (@DesignedEntry_800d6954) := I.
Global Typeclasses Opaque DesignedEntry_800d6954.

Lemma DesignedBoundary_800d6954 `{!islaG Sigma} `{!threadG} (args : KeysToOwnedSliceBlockArgs) (returnAddress : Z) (K : iProp Sigma)  :
  instr_pre 0x800d6908 (ZesuSsz.Generated.KeysToOwnedSlice.FP301.Pilot018cEntries.fp_machineAt018c (args) (returnAddress) (K))%I -∗
  instr_pre 0x800d695c (ZesuSsz.Generated.KeysToOwnedSlice.FP301.Pilot01e0Entries.fp_machineAt01e0 (args) (returnAddress) (K))%I -∗
  keysToOwnedSliceSelectedCode -∗
  instr_body 0x800d6954
    (DesignedEntry_800d6954 args returnAddress K).
Proof.
  zesu_block2.
Qed.

Print Assumptions DesignedBoundary_800d6954.
