Require Import ZesuSsz.Generated.KeysToOwnedSliceBudget.FP301.Pilot007cEntries.
Require Import ZesuSsz.Generated.KeysToOwnedSliceBudget.FP301.Pilot007cStructural.
Require Import ZesuSsz.Generated.KeysToOwnedSliceBudget.FP301.Pilot0098Entries.
Require Import ZesuSsz.Generated.KeysToOwnedSliceBudget.FP301.Pilot0098Structural.
Require Import ZesuSsz.Contracts.AltFlAllocPremises.
Require Import ZesuSsz.Automation2.StepBudget.
Require Import ZesuSsz.Automation2.All.
Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith NArith.NArith.
Require Import stdpp.bitvector.definitions.
Require Import ZesuSsz.Contracts.KeysToOwnedSliceBlockEntries.
Require Import ZesuSsz.Contracts.KeysToOwnedSliceChargedSelected.
Require Import ZesuSsz.Generated.KeysToOwnedSliceBudget.FP301.Edges007c.
Require Import ZesuSsz.Automation2.All.
Local Open Scope Z_scope.
#[local] Typeclasses Transparent keysToOwnedSliceChargedCode.

Definition DesignedEntry_800d67f8
    `{!islaG Sigma} `{!threadG} (args : KeysToOwnedSliceBlockArgs) (returnAddress : Z) (K : iProp Sigma) : iProp Sigma :=
  ((ZesuSsz.Generated.KeysToOwnedSliceBudget.FP301.Pilot007cEntries.fp_machineAt007c (args) (returnAddress) (K)) ∗
   True)%I.
Global Instance : LithiumUnfold (@DesignedEntry_800d67f8) := I.
Global Typeclasses Opaque DesignedEntry_800d67f8.

Lemma DesignedBoundary_800d67f8 `{!islaG Sigma} `{!threadG} (args : KeysToOwnedSliceBlockArgs) (returnAddress : Z) (K : iProp Sigma)  :
  instr_pre 0x800d6814 (ZesuSsz.Generated.KeysToOwnedSliceBudget.FP301.Pilot0098Entries.fp_machineAt0098 (args) (returnAddress) (K))%I -∗
  instr_pre 0x80041f38 (step_budget (42) ∗ ZesuSsz.Contracts.AltFlAllocPremises.altFlFreeCallSpec)%I -∗
  keysToOwnedSliceChargedCode -∗
  instr_body 0x800d67f8
    (DesignedEntry_800d67f8 args returnAddress K).
Proof.
  zesu_block2.
Qed.

Print Assumptions DesignedBoundary_800d67f8.
