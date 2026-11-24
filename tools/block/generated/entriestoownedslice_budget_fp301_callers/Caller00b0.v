Require Import ZesuSsz.Generated.EntriesToOwnedSliceBudget.FP301.Pilot00b0Entries.
Require Import ZesuSsz.Generated.EntriesToOwnedSliceBudget.FP301.Pilot00b0Structural.
Require Import ZesuSsz.Generated.EntriesToOwnedSliceBudget.FP301.Pilot00e4Entries.
Require Import ZesuSsz.Generated.EntriesToOwnedSliceBudget.FP301.Pilot00e4Structural.
Require Import ZesuSsz.Contracts.AltFlAllocPremises.
Require Import ZesuSsz.Automation2.StepBudget.
Require Import ZesuSsz.Automation2.All.
Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith NArith.NArith.
Require Import stdpp.bitvector.definitions.
Require Import ZesuSsz.Contracts.EntriesToOwnedSliceBlockEntries.
Require Import ZesuSsz.Contracts.EntriesToOwnedSliceChargedSelected.
Require Import ZesuSsz.Generated.EntriesToOwnedSliceBudget.FP301.Edges00b0.
Require Import ZesuSsz.Automation2.All.
Local Open Scope Z_scope.
#[local] Typeclasses Transparent entriesToOwnedSliceChargedCode.

Definition DesignedEntry_800d6604
    `{!islaG Sigma} `{!threadG} (args : EntriesToOwnedSliceBlockArgs) (returnAddress : Z) (K : iProp Sigma) : iProp Sigma :=
  ((ZesuSsz.Generated.EntriesToOwnedSliceBudget.FP301.Pilot00b0Entries.fp_machineAt00b0 (args) (returnAddress) (K)) ∗
   True)%I.
Global Instance : LithiumUnfold (@DesignedEntry_800d6604) := I.
Global Typeclasses Opaque DesignedEntry_800d6604.

Lemma DesignedBoundary_800d6604 `{!islaG Sigma} `{!threadG} (args : EntriesToOwnedSliceBlockArgs) (returnAddress : Z) (K : iProp Sigma)  :
  instr_pre 0x800d6638 (ZesuSsz.Generated.EntriesToOwnedSliceBudget.FP301.Pilot00e4Entries.fp_machineAt00e4 (args) (returnAddress) (K))%I -∗
  instr_pre 0x8004218c (step_budget (9) ∗ ZesuSsz.Contracts.AltFlAllocPremises.altFlRemapCallSpec)%I -∗
  entriesToOwnedSliceChargedCode -∗
  instr_body 0x800d6604
    (DesignedEntry_800d6604 args returnAddress K).
Proof.
  zesu_block2.
Qed.

Print Assumptions DesignedBoundary_800d6604.
