Require Import ZesuSsz.Generated.KeysToOwnedSliceBudget.FP301.Pilot0168Entries.
Require Import ZesuSsz.Generated.KeysToOwnedSliceBudget.FP301.Pilot0168Structural.
Require Import ZesuSsz.Generated.KeysToOwnedSliceBudget.FP301.Pilot0110Entries.
Require Import ZesuSsz.Generated.KeysToOwnedSliceBudget.FP301.Pilot0110Structural.
Require Import ZesuSsz.Generated.KeysToOwnedSliceBudget.FP301.Pilot0170Entries.
Require Import ZesuSsz.Generated.KeysToOwnedSliceBudget.FP301.Pilot0170Structural.
Require Import ZesuSsz.Automation2.StepBudget.
Require Import ZesuSsz.Automation2.All.
Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith NArith.NArith.
Require Import stdpp.bitvector.definitions.
Require Import ZesuSsz.Contracts.KeysToOwnedSliceBlockEntries.
Require Import ZesuSsz.Contracts.KeysToOwnedSliceChargedSelected.
Require Import ZesuSsz.Generated.KeysToOwnedSliceBudget.FP301.Edges0168.
Require Import ZesuSsz.Automation2.All.
Local Open Scope Z_scope.
#[local] Typeclasses Transparent keysToOwnedSliceChargedCode.

Definition DesignedEntry_800d68e4
    `{!islaG Sigma} `{!threadG} (args : KeysToOwnedSliceBlockArgs) (returnAddress : Z) (K : iProp Sigma) : iProp Sigma :=
  ((ZesuSsz.Generated.KeysToOwnedSliceBudget.FP301.Pilot0168Entries.fp_machineAt0168 (args) (returnAddress) (K)) ∗
   True)%I.
Global Instance : LithiumUnfold (@DesignedEntry_800d68e4) := I.
Global Typeclasses Opaque DesignedEntry_800d68e4.

Lemma DesignedBoundary_800d68e4 `{!islaG Sigma} `{!threadG} (args : KeysToOwnedSliceBlockArgs) (returnAddress : Z) (K : iProp Sigma)  :
  instr_pre 0x800d688c (ZesuSsz.Generated.KeysToOwnedSliceBudget.FP301.Pilot0110Entries.fp_machineAt0110 (args) (returnAddress) (K))%I -∗
  instr_pre 0x800d68ec (ZesuSsz.Generated.KeysToOwnedSliceBudget.FP301.Pilot0170Entries.fp_machineAt0170 (args) (returnAddress) (K))%I -∗
  keysToOwnedSliceChargedCode -∗
  instr_body 0x800d68e4
    (DesignedEntry_800d68e4 args returnAddress K).
Proof.
  zesu_block2.
Qed.

Print Assumptions DesignedBoundary_800d68e4.
