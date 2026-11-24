Require Import ZesuSsz.Generated.EntriesToOwnedSliceBudget.FP301.Pilot01acEntries.
Require Import ZesuSsz.Generated.EntriesToOwnedSliceBudget.FP301.Pilot01acStructural.
Require Import ZesuSsz.Generated.EntriesToOwnedSliceBudget.FP301.Pilot01c0Entries.
Require Import ZesuSsz.Generated.EntriesToOwnedSliceBudget.FP301.Pilot01c0Structural.
Require Import ZesuSsz.Contracts.ZiskMemcpyPremise.
Require Import ZesuSsz.Automation2.StepBudget.
Require Import ZesuSsz.Automation2.All.
Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith NArith.NArith.
Require Import stdpp.bitvector.definitions.
Require Import ZesuSsz.Contracts.EntriesToOwnedSliceBlockEntries.
Require Import ZesuSsz.Contracts.EntriesToOwnedSliceChargedSelected.
Require Import ZesuSsz.Generated.EntriesToOwnedSliceBudget.FP301.Edges01ac.
Require Import ZesuSsz.Automation2.All.
Require Import ZesuSsz.Residuals.entriesToOwnedSlice.Block01ac.
Local Open Scope Z_scope.
#[local] Typeclasses Transparent entriesToOwnedSliceChargedCode.

Definition DesignedEntry_800d6700
    `{!islaG Sigma} `{!threadG} (args : EntriesToOwnedSliceBlockArgs) (returnAddress : Z) (K : iProp Sigma) : iProp Sigma :=
  ((ZesuSsz.Generated.EntriesToOwnedSliceBudget.FP301.Pilot01acEntries.fp_machineAt01ac (args) (returnAddress) (K)) ∗
   True)%I.
Global Instance : LithiumUnfold (@DesignedEntry_800d6700) := I.
Global Typeclasses Opaque DesignedEntry_800d6700.

Lemma DesignedBoundary_800d6700 `{!islaG Sigma} `{!threadG} (args : EntriesToOwnedSliceBlockArgs) (returnAddress : Z) (K : iProp Sigma)  :
  instr_pre 0x800d6714 (ZesuSsz.Generated.EntriesToOwnedSliceBudget.FP301.Pilot01c0Entries.fp_machineAt01c0 (args) (returnAddress) (K))%I -∗
  instr_pre 0x800e06c0 (step_budget (3) ∗ ZesuSsz.Contracts.ZiskMemcpyPremise.ziskMemcpyCallSpec)%I -∗
  entriesToOwnedSliceChargedCode -∗
  instr_body 0x800d6700
    (DesignedEntry_800d6700 args returnAddress K).
Proof.
  zesu_block2.
Qed.

Print Assumptions DesignedBoundary_800d6700.
