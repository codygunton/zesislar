Require Import ZesuSsz.Generated.KeysToOwnedSliceBudget.FP301.Pilot00d8Entries.
Require Import ZesuSsz.Generated.KeysToOwnedSliceBudget.FP301.Pilot00d8Structural.
Require Import ZesuSsz.Generated.KeysToOwnedSliceBudget.FP301.Pilot00f0Entries.
Require Import ZesuSsz.Generated.KeysToOwnedSliceBudget.FP301.Pilot00f0Structural.
Require Import ZesuSsz.Automation2.StepBudget.
Require Import ZesuSsz.Automation2.All.
Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith NArith.NArith.
Require Import stdpp.bitvector.definitions.
Require Import ZesuSsz.Contracts.KeysToOwnedSliceBlockEntries.
Require Import ZesuSsz.Contracts.KeysToOwnedSliceChargedSelected.
Require Import ZesuSsz.Generated.KeysToOwnedSliceBudget.FP301.Edges00d8.
Require Import ZesuSsz.Automation2.All.
Local Open Scope Z_scope.
#[local] Typeclasses Transparent keysToOwnedSliceChargedCode.

Definition DesignedEntry_800d6854
    `{!islaG Sigma} `{!threadG} (args : KeysToOwnedSliceBlockArgs) (returnAddress : Z) (K : iProp Sigma) : iProp Sigma :=
  ((ZesuSsz.Generated.KeysToOwnedSliceBudget.FP301.Pilot00d8Entries.fp_machineAt00d8 (args) (returnAddress) (K)) ∗
   True)%I.
Global Instance : LithiumUnfold (@DesignedEntry_800d6854) := I.
Global Typeclasses Opaque DesignedEntry_800d6854.

Lemma DesignedBoundary_800d6854 `{!islaG Sigma} `{!threadG} (args : KeysToOwnedSliceBlockArgs) (returnAddress : Z) (K : iProp Sigma)  :
  instr_pre 0x800d686c (ZesuSsz.Generated.KeysToOwnedSliceBudget.FP301.Pilot00f0Entries.fp_machineAt00f0_slot0 (args) (returnAddress) (K))%I -∗
  keysToOwnedSliceChargedCode -∗
  instr_body 0x800d6854
    (DesignedEntry_800d6854 args returnAddress K).
Proof.
  zesu_block2.
Qed.

Print Assumptions DesignedBoundary_800d6854.
