Require Import ZesuSsz.Generated.KeysEnsureCapacityBudget.FP301.Pilot00c0Entries.
Require Import ZesuSsz.Generated.KeysEnsureCapacityBudget.FP301.Pilot00c0Structural.
Require Import ZesuSsz.Generated.KeysEnsureCapacityBudget.FP301.Pilot00ecEntries.
Require Import ZesuSsz.Generated.KeysEnsureCapacityBudget.FP301.Pilot00ecStructural.
Require Import ZesuSsz.Contracts.AltFlAllocPremises.
Require Import ZesuSsz.Automation2.StepBudget.
Require Import ZesuSsz.Automation2.All.
Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith NArith.NArith.
Require Import stdpp.bitvector.definitions.
Require Import ZesuSsz.Contracts.KeysEnsureCapacityBlockEntries.
Require Import ZesuSsz.Contracts.KeysEnsureCapacityChargedSelected.
Require Import ZesuSsz.Generated.KeysEnsureCapacityBudget.FP301.Edges00c0.
Require Import ZesuSsz.Automation2.All.
Local Open Scope Z_scope.
#[local] Typeclasses Transparent keysEnsureCapacityChargedCode.

Definition DesignedEntry_800cb4cc
    `{!islaG Sigma} `{!threadG} (args : KeysEnsureCapacityBlockArgs) (returnAddress : Z) (K : iProp Sigma) : iProp Sigma :=
  ((ZesuSsz.Generated.KeysEnsureCapacityBudget.FP301.Pilot00c0Entries.fp_machineAt00c0 (args) (returnAddress) (K)) ∗
   True)%I.
Global Instance : LithiumUnfold (@DesignedEntry_800cb4cc) := I.
Global Typeclasses Opaque DesignedEntry_800cb4cc.

Lemma DesignedBoundary_800cb4cc `{!islaG Sigma} `{!threadG} (args : KeysEnsureCapacityBlockArgs) (returnAddress : Z) (K : iProp Sigma)  :
  instr_pre 0x800cb4f8 (ZesuSsz.Generated.KeysEnsureCapacityBudget.FP301.Pilot00ecEntries.fp_machineAt00ec (args) (returnAddress) (K))%I -∗
  instr_pre 0x8004218c (step_budget (9) ∗ ZesuSsz.Contracts.AltFlAllocPremises.altFlRemapCallSpec)%I -∗
  keysEnsureCapacityChargedCode -∗
  instr_body 0x800cb4cc
    (DesignedEntry_800cb4cc args returnAddress K).
Proof.
  zesu_block2.
Qed.

Print Assumptions DesignedBoundary_800cb4cc.
