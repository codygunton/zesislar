Require Import ZesuSsz.Generated.EntriesToOwnedSliceBudget.FP301.Pilot007cEntries.
Require Import ZesuSsz.Generated.EntriesToOwnedSliceBudget.FP301.Pilot007cStructural.
Require Import ZesuSsz.Generated.EntriesToOwnedSliceBudget.FP301.Pilot0080Entries.
Require Import ZesuSsz.Generated.EntriesToOwnedSliceBudget.FP301.Pilot0080Structural.
Require Import ZesuSsz.Generated.EntriesToOwnedSliceBudget.FP301.Pilot00a4Entries.
Require Import ZesuSsz.Generated.EntriesToOwnedSliceBudget.FP301.Pilot00a4Structural.
Require Import ZesuSsz.Automation2.StepBudget.
Require Import ZesuSsz.Automation2.All.
Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith NArith.NArith.
Require Import stdpp.bitvector.definitions.
Require Import ZesuSsz.Contracts.EntriesToOwnedSliceBlockEntries.
Require Import ZesuSsz.Contracts.EntriesToOwnedSliceChargedSelected.
Require Import ZesuSsz.Generated.EntriesToOwnedSliceBudget.FP301.Edges007c.
Require Import ZesuSsz.Automation2.All.
Require Import ZesuSsz.Residuals.entriesToOwnedSlice.Block007c.
Local Open Scope Z_scope.
#[local] Typeclasses Transparent entriesToOwnedSliceChargedCode.

Definition DesignedEntry_800d65d0
    `{!islaG Sigma} `{!threadG} (args : EntriesToOwnedSliceBlockArgs) (returnAddress : Z) (K : iProp Sigma) : iProp Sigma :=
  ((ZesuSsz.Generated.EntriesToOwnedSliceBudget.FP301.Pilot007cEntries.fp_machineAt007c (args) (returnAddress) (K)) ∗
   True)%I.
Global Instance : LithiumUnfold (@DesignedEntry_800d65d0) := I.
Global Typeclasses Opaque DesignedEntry_800d65d0.

Lemma DesignedBoundary_800d65d0 `{!islaG Sigma} `{!threadG} (args : EntriesToOwnedSliceBlockArgs) (returnAddress : Z) (K : iProp Sigma)  :
  instr_pre 0x800d65d4 (ZesuSsz.Generated.EntriesToOwnedSliceBudget.FP301.Pilot0080Entries.fp_machineAt0080 (args) (returnAddress) (K))%I -∗
  instr_pre 0x800d65f8 (ZesuSsz.Generated.EntriesToOwnedSliceBudget.FP301.Pilot00a4Entries.fp_machineAt00a4 (args) (returnAddress) (K))%I -∗
  entriesToOwnedSliceChargedCode -∗
  instr_body 0x800d65d0
    (DesignedEntry_800d65d0 args returnAddress K).
Proof.
  zesu_block2.
Qed.

Print Assumptions DesignedBoundary_800d65d0.
