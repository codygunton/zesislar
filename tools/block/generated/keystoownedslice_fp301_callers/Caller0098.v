Require Import ZesuSsz.Generated.KeysToOwnedSlice.FP301.Pilot0098Entries.
Require Import ZesuSsz.Generated.KeysToOwnedSlice.FP301.Pilot0098Structural.
Require Import ZesuSsz.Generated.KeysToOwnedSlice.FP301.Pilot00a0Entries.
Require Import ZesuSsz.Generated.KeysToOwnedSlice.FP301.Pilot00a0Structural.
Require Import ZesuSsz.Generated.KeysToOwnedSlice.FP301.Pilot00d8Entries.
Require Import ZesuSsz.Generated.KeysToOwnedSlice.FP301.Pilot00d8Structural.
Require Import ZesuSsz.Automation2.All.
Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith NArith.NArith.
Require Import stdpp.bitvector.definitions.
Require Import ZesuSsz.Contracts.KeysToOwnedSliceBlockEntries.
Require Import ZesuSsz.Contracts.KeysToOwnedSliceSelected.
Require Import ZesuSsz.Generated.KeysToOwnedSlice.FP301.Edges0098.
Require Import ZesuSsz.Automation2.All.
Require Import ZesuSsz.Residuals.keysToOwnedSlice.Block0098.
Local Open Scope Z_scope.
#[local] Typeclasses Transparent keysToOwnedSliceSelectedCode.

Definition DesignedEntry_800d6814
    `{!islaG Sigma} `{!threadG} (args : KeysToOwnedSliceBlockArgs) (returnAddress : Z) (K : iProp Sigma) : iProp Sigma :=
  ((ZesuSsz.Generated.KeysToOwnedSlice.FP301.Pilot0098Entries.fp_machineAt0098 (args) (returnAddress) (K)) ∗
   True)%I.
Global Instance : LithiumUnfold (@DesignedEntry_800d6814) := I.
Global Typeclasses Opaque DesignedEntry_800d6814.

Lemma DesignedBoundary_800d6814 `{!islaG Sigma} `{!threadG} (args : KeysToOwnedSliceBlockArgs) (returnAddress : Z) (K : iProp Sigma)  :
  instr_pre 0x800d681c (ZesuSsz.Generated.KeysToOwnedSlice.FP301.Pilot00a0Entries.fp_machineAt00a0 (args) (returnAddress) (K))%I -∗
  instr_pre 0x800d6854 (ZesuSsz.Generated.KeysToOwnedSlice.FP301.Pilot00d8Entries.fp_machineAt00d8 (args) (returnAddress) (K))%I -∗
  keysToOwnedSliceSelectedCode -∗
  instr_body 0x800d6814
    (DesignedEntry_800d6814 args returnAddress K).
Proof.
  zesu_block2.
Qed.

Print Assumptions DesignedBoundary_800d6814.
