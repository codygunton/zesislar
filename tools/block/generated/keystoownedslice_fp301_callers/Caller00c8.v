Require Import ZesuSsz.Generated.KeysToOwnedSlice.FP301.Pilot00c8Entries.
Require Import ZesuSsz.Generated.KeysToOwnedSlice.FP301.Pilot00c8Structural.
Require Import ZesuSsz.Generated.KeysToOwnedSlice.FP301.Pilot00ccEntries.
Require Import ZesuSsz.Generated.KeysToOwnedSlice.FP301.Pilot00ccStructural.
Require Import ZesuSsz.Generated.KeysToOwnedSlice.FP301.Pilot00f8Entries.
Require Import ZesuSsz.Generated.KeysToOwnedSlice.FP301.Pilot00f8Structural.
Require Import ZesuSsz.Automation2.All.
Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith NArith.NArith.
Require Import stdpp.bitvector.definitions.
Require Import ZesuSsz.Contracts.KeysToOwnedSliceBlockEntries.
Require Import ZesuSsz.Contracts.KeysToOwnedSliceSelected.
Require Import ZesuSsz.Generated.KeysToOwnedSlice.FP301.Edges00c8.
Require Import ZesuSsz.Automation2.All.
Local Open Scope Z_scope.
#[local] Typeclasses Transparent keysToOwnedSliceSelectedCode.

Definition DesignedEntry_800d6844
    `{!islaG Sigma} `{!threadG} (args : KeysToOwnedSliceBlockArgs) (returnAddress : Z) (K : iProp Sigma) : iProp Sigma :=
  ((ZesuSsz.Generated.KeysToOwnedSlice.FP301.Pilot00c8Entries.fp_machineAt00c8 (args) (returnAddress) (K)) ∗
   True)%I.
Global Instance : LithiumUnfold (@DesignedEntry_800d6844) := I.
Global Typeclasses Opaque DesignedEntry_800d6844.

Lemma DesignedBoundary_800d6844 `{!islaG Sigma} `{!threadG} (args : KeysToOwnedSliceBlockArgs) (returnAddress : Z) (K : iProp Sigma)  :
  instr_pre 0x800d6848 (ZesuSsz.Generated.KeysToOwnedSlice.FP301.Pilot00ccEntries.fp_machineAt00cc (args) (returnAddress) (K))%I -∗
  instr_pre 0x800d6874 (ZesuSsz.Generated.KeysToOwnedSlice.FP301.Pilot00f8Entries.fp_machineAt00f8 (args) (returnAddress) (K))%I -∗
  keysToOwnedSliceSelectedCode -∗
  instr_body 0x800d6844
    (DesignedEntry_800d6844 args returnAddress K).
Proof.
  zesu_block2.
Qed.

Print Assumptions DesignedBoundary_800d6844.
