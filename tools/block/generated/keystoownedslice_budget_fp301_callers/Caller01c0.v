Require Import ZesuSsz.Generated.KeysToOwnedSliceBudget.FP301.Pilot01c0Entries.
Require Import ZesuSsz.Generated.KeysToOwnedSliceBudget.FP301.Pilot01c0Structural.
Require Import ZesuSsz.Generated.KeysToOwnedSliceBudget.FP301.Pilot01d8Entries.
Require Import ZesuSsz.Generated.KeysToOwnedSliceBudget.FP301.Pilot01d8Structural.
Require Import ZesuSsz.Contracts.ZiskMemcpyPremise.
Require Import ZesuSsz.Automation2.StepBudget.
Require Import ZesuSsz.Automation2.All.
Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith NArith.NArith.
Require Import stdpp.bitvector.definitions.
Require Import ZesuSsz.Contracts.KeysToOwnedSliceBlockEntries.
Require Import ZesuSsz.Contracts.KeysToOwnedSliceChargedSelected.
Require Import ZesuSsz.Automation2.All.
Local Open Scope Z_scope.
#[local] Typeclasses Transparent keysToOwnedSliceChargedCode.

Definition DesignedEntry_800d693c
    `{!islaG Sigma} `{!threadG} (args : KeysToOwnedSliceBlockArgs) (returnAddress : Z) (K : iProp Sigma) : iProp Sigma :=
  ((ZesuSsz.Generated.KeysToOwnedSliceBudget.FP301.Pilot01c0Entries.fp_machineAt01c0 (args) (returnAddress) (K)) ∗
   True)%I.
Global Instance : LithiumUnfold (@DesignedEntry_800d693c) := I.
Global Typeclasses Opaque DesignedEntry_800d693c.

Lemma DesignedBoundary_800d693c `{!islaG Sigma} `{!threadG} (args : KeysToOwnedSliceBlockArgs) (returnAddress : Z) (K : iProp Sigma)  :
  instr_pre 0x800d6954 (ZesuSsz.Generated.KeysToOwnedSliceBudget.FP301.Pilot01d8Entries.fp_machineAt01d8 (args) (returnAddress) (K))%I -∗
  instr_pre 0x800e06c0 (step_budget (3) ∗ ZesuSsz.Contracts.ZiskMemcpyPremise.ziskMemcpyCallSpec)%I -∗
  keysToOwnedSliceChargedCode -∗
  instr_body 0x800d693c
    (DesignedEntry_800d693c args returnAddress K).
Proof.
  zesu_block2.
Qed.

Print Assumptions DesignedBoundary_800d693c.
