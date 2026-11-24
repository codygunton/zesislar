Require Import ZesuSsz.Generated.EntriesToOwnedSliceBudget.FP301.Pilot0108Entries.
Require Import ZesuSsz.Generated.EntriesToOwnedSliceBudget.FP301.Pilot0108Structural.
Require Import ZesuSsz.Generated.EntriesToOwnedSliceBudget.FP301.Pilot0120Entries.
Require Import ZesuSsz.Generated.EntriesToOwnedSliceBudget.FP301.Pilot0120Structural.
Require Import ZesuSsz.Automation2.StepBudget.
Require Import ZesuSsz.Automation2.All.
Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith NArith.NArith.
Require Import stdpp.bitvector.definitions.
Require Import ZesuSsz.Contracts.EntriesToOwnedSliceBlockEntries.
Require Import ZesuSsz.Contracts.EntriesToOwnedSliceChargedSelected.
Require Import ZesuSsz.Generated.EntriesToOwnedSliceBudget.FP301.Edges0108.
Require Import ZesuSsz.Automation2.All.
Local Open Scope Z_scope.
#[local] Typeclasses Transparent entriesToOwnedSliceChargedCode.

Definition DesignedEntry_800d665c
    `{!islaG Sigma} `{!threadG} (args : EntriesToOwnedSliceBlockArgs) (returnAddress : Z) (K : iProp Sigma) : iProp Sigma :=
  ((ZesuSsz.Generated.EntriesToOwnedSliceBudget.FP301.Pilot0108Entries.fp_machineAt0108 (args) (returnAddress) (K)) ∗
   True)%I.
Global Instance : LithiumUnfold (@DesignedEntry_800d665c) := I.
Global Typeclasses Opaque DesignedEntry_800d665c.

Lemma DesignedBoundary_800d665c `{!islaG Sigma} `{!threadG} (args : EntriesToOwnedSliceBlockArgs) (returnAddress : Z) (K : iProp Sigma)  :
  instr_pre 0x800d6674 (ZesuSsz.Generated.EntriesToOwnedSliceBudget.FP301.Pilot0120Entries.fp_machineAt0120_slot0 (args) (returnAddress) (K))%I -∗
  entriesToOwnedSliceChargedCode -∗
  instr_body 0x800d665c
    (DesignedEntry_800d665c args returnAddress K).
Proof.
  zesu_block2.
Qed.

Print Assumptions DesignedBoundary_800d665c.
