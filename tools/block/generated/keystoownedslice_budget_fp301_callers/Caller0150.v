Require Import ZesuSsz.Generated.KeysToOwnedSliceBudget.FP301.Pilot0150Entries.
Require Import ZesuSsz.Generated.KeysToOwnedSliceBudget.FP301.Pilot0150Structural.
Require Import ZesuSsz.Generated.KeysToOwnedSliceBudget.FP301.Pilot0168Entries.
Require Import ZesuSsz.Generated.KeysToOwnedSliceBudget.FP301.Pilot0168Structural.
Require Import ZesuSsz.Contracts.AltFlAllocPremises.
Require Import ZesuSsz.Automation2.StepBudget.
Require Import ZesuSsz.Automation2.All.
Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith NArith.NArith.
Require Import stdpp.bitvector.definitions.
Require Import ZesuSsz.Contracts.KeysToOwnedSliceBlockEntries.
Require Import ZesuSsz.Contracts.KeysToOwnedSliceChargedSelected.
Require Import ZesuSsz.Generated.KeysToOwnedSliceBudget.FP301.Edges0150.
Require Import ZesuSsz.Automation2.All.
Require Import ZesuSsz.Residuals.keysToOwnedSlice.Block0150.
Local Open Scope Z_scope.
#[local] Typeclasses Transparent keysToOwnedSliceChargedCode.

Definition DesignedEntry_800d68cc
    `{!islaG Sigma} `{!threadG} (args : KeysToOwnedSliceBlockArgs) (returnAddress : Z) (K : iProp Sigma) : iProp Sigma :=
  ((ZesuSsz.Generated.KeysToOwnedSliceBudget.FP301.Pilot0150Entries.fp_machineAt0150 (args) (returnAddress) (K)) ∗
   True)%I.
Global Instance : LithiumUnfold (@DesignedEntry_800d68cc) := I.
Global Typeclasses Opaque DesignedEntry_800d68cc.

Lemma DesignedBoundary_800d68cc `{!islaG Sigma} `{!threadG} (args : KeysToOwnedSliceBlockArgs) (returnAddress : Z) (K : iProp Sigma)  :
  instr_pre 0x800d68e4 (ZesuSsz.Generated.KeysToOwnedSliceBudget.FP301.Pilot0168Entries.fp_machineAt0168 (args) (returnAddress) (K))%I -∗
  instr_pre 0x80042494 (step_budget (53) ∗ ZesuSsz.Contracts.AltFlAllocPremises.altFlAllocCallSpec)%I -∗
  keysToOwnedSliceChargedCode -∗
  instr_body 0x800d68cc
    (DesignedEntry_800d68cc args returnAddress K).
Proof.
  zesu_block2.
Qed.

Print Assumptions DesignedBoundary_800d68cc.
