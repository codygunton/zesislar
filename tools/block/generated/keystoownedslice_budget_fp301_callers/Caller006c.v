Require Import ZesuSsz.Generated.KeysToOwnedSliceBudget.FP301.Pilot006cEntries.
Require Import ZesuSsz.Generated.KeysToOwnedSliceBudget.FP301.Pilot006cStructural.
Require Import ZesuSsz.Generated.KeysToOwnedSliceBudget.FP301.Pilot00fcEntries.
Require Import ZesuSsz.Generated.KeysToOwnedSliceBudget.FP301.Pilot00fcStructural.
Require Import ZesuSsz.Automation2.StepBudget.
Require Import ZesuSsz.Automation2.All.
Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith NArith.NArith.
Require Import stdpp.bitvector.definitions.
Require Import ZesuSsz.Contracts.KeysToOwnedSliceBlockEntries.
Require Import ZesuSsz.Contracts.KeysToOwnedSliceChargedSelected.
Require Import ZesuSsz.Generated.KeysToOwnedSliceBudget.FP301.Edges006c.
Require Import ZesuSsz.Automation2.All.
Local Open Scope Z_scope.
#[local] Typeclasses Transparent keysToOwnedSliceChargedCode.

Definition DesignedEntry_800d67e8
    `{!islaG Sigma} `{!threadG} (args : KeysToOwnedSliceBlockArgs) (returnAddress : Z) (K : iProp Sigma) : iProp Sigma :=
  ((ZesuSsz.Generated.KeysToOwnedSliceBudget.FP301.Pilot006cEntries.fp_machineAt006c (args) (returnAddress) (K)) ∗
   True)%I.
Global Instance : LithiumUnfold (@DesignedEntry_800d67e8) := I.
Global Typeclasses Opaque DesignedEntry_800d67e8.

Lemma DesignedBoundary_800d67e8 `{!islaG Sigma} `{!threadG} (args : KeysToOwnedSliceBlockArgs) (returnAddress : Z) (K : iProp Sigma)  :
  instr_pre 0x800d6878 (ZesuSsz.Generated.KeysToOwnedSliceBudget.FP301.Pilot00fcEntries.fp_machineAt00fc (args) (returnAddress) (K))%I -∗
  keysToOwnedSliceChargedCode -∗
  instr_body 0x800d67e8
    (DesignedEntry_800d67e8 args returnAddress K).
Proof.
  zesu_block2.
Qed.

Print Assumptions DesignedBoundary_800d67e8.
