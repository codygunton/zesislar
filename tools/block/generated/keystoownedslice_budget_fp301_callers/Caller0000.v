Require Import ZesuSsz.Generated.KeysToOwnedSliceBudget.FP301.Pilot0000Entries.
Require Import ZesuSsz.Generated.KeysToOwnedSliceBudget.FP301.Pilot0000Structural.
Require Import ZesuSsz.Generated.KeysToOwnedSliceBudget.FP301.Pilot0058Entries.
Require Import ZesuSsz.Generated.KeysToOwnedSliceBudget.FP301.Pilot0058Structural.
Require Import ZesuSsz.Generated.KeysToOwnedSliceBudget.FP301.Pilot0078Entries.
Require Import ZesuSsz.Generated.KeysToOwnedSliceBudget.FP301.Pilot0078Structural.
Require Import ZesuSsz.Automation2.StepBudget.
Require Import ZesuSsz.Automation2.All.
Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith NArith.NArith.
Require Import stdpp.bitvector.definitions.
Require Import ZesuSsz.Contracts.KeysToOwnedSliceBlockEntries.
Require Import ZesuSsz.Contracts.KeysToOwnedSliceChargedSelected.
Require Import ZesuSsz.Generated.KeysToOwnedSliceBudget.FP301.Edges0000.
Require Import ZesuSsz.Automation2.All.
Require Import ZesuSsz.Residuals.keysToOwnedSlice.Block0000.
Local Open Scope Z_scope.
#[local] Typeclasses Transparent keysToOwnedSliceChargedCode.

Definition DesignedEntry_800d677c
    `{!islaG Sigma} `{!threadG} (args : KeysToOwnedSliceBlockArgs) (returnAddress : Z) (K : iProp Sigma) : iProp Sigma :=
  ((ZesuSsz.Generated.KeysToOwnedSliceBudget.FP301.Pilot0000Entries.fp_machineAt0000 (args) (returnAddress) (K)) ∗
   True)%I.
Global Instance : LithiumUnfold (@DesignedEntry_800d677c) := I.
Global Typeclasses Opaque DesignedEntry_800d677c.

Lemma DesignedBoundary_800d677c `{!islaG Sigma} `{!threadG} (args : KeysToOwnedSliceBlockArgs) (returnAddress : Z) (K : iProp Sigma)  :
  instr_pre 0x800d67d4 (ZesuSsz.Generated.KeysToOwnedSliceBudget.FP301.Pilot0058Entries.fp_machineAt0058 (args) (returnAddress) (K))%I -∗
  instr_pre 0x800d67f4 (ZesuSsz.Generated.KeysToOwnedSliceBudget.FP301.Pilot0078Entries.fp_machineAt0078 (args) (returnAddress) (K))%I -∗
  keysToOwnedSliceChargedCode -∗
  instr_body 0x800d677c
    (DesignedEntry_800d677c args returnAddress K).
Proof.
  zesu_block2.
Qed.

Print Assumptions DesignedBoundary_800d677c.
