Require Import ZesuSsz.Generated.KeysEnsureCapacity.FP301.Pilot00ecEntries.
Require Import ZesuSsz.Generated.KeysEnsureCapacity.FP301.Pilot00ecStructural.
Require Import ZesuSsz.Generated.KeysEnsureCapacity.FP301.Pilot00f0Entries.
Require Import ZesuSsz.Generated.KeysEnsureCapacity.FP301.Pilot00f0Structural.
Require Import ZesuSsz.Generated.KeysEnsureCapacity.FP301.Pilot0108Entries.
Require Import ZesuSsz.Generated.KeysEnsureCapacity.FP301.Pilot0108Structural.
Require Import ZesuSsz.Automation2.All.
Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith NArith.NArith.
Require Import stdpp.bitvector.definitions.
Require Import ZesuSsz.Contracts.KeysEnsureCapacityBlockEntries.
Require Import ZesuSsz.Contracts.KeysEnsureCapacitySelected.
Require Import ZesuSsz.Generated.KeysEnsureCapacity.FP301.Edges00ec.
Require Import ZesuSsz.Automation2.All.
Local Open Scope Z_scope.
#[local] Typeclasses Transparent keysEnsureCapacitySelectedCode.

Definition DesignedEntry_800cb4f8
    `{!islaG Sigma} `{!threadG} (args : KeysEnsureCapacityBlockArgs) (returnAddress : Z) (K : iProp Sigma) : iProp Sigma :=
  ((ZesuSsz.Generated.KeysEnsureCapacity.FP301.Pilot00ecEntries.fp_machineAt00ec (args) (returnAddress) (K)) ∗
   True)%I.
Global Instance : LithiumUnfold (@DesignedEntry_800cb4f8) := I.
Global Typeclasses Opaque DesignedEntry_800cb4f8.

Lemma DesignedBoundary_800cb4f8 `{!islaG Sigma} `{!threadG} (args : KeysEnsureCapacityBlockArgs) (returnAddress : Z) (K : iProp Sigma)  :
  instr_pre 0x800cb4fc (ZesuSsz.Generated.KeysEnsureCapacity.FP301.Pilot00f0Entries.fp_machineAt00f0 (args) (returnAddress) (K))%I -∗
  instr_pre 0x800cb514 (ZesuSsz.Generated.KeysEnsureCapacity.FP301.Pilot0108Entries.fp_machineAt0108 (args) (returnAddress) (K))%I -∗
  keysEnsureCapacitySelectedCode -∗
  instr_body 0x800cb4f8
    (DesignedEntry_800cb4f8 args returnAddress K).
Proof.
  zesu_block2.
Qed.

Print Assumptions DesignedBoundary_800cb4f8.
