Require Import ZesuSsz.Generated.KeysEnsureCapacity.FP301.Pilot0138Entries.
Require Import ZesuSsz.Generated.KeysEnsureCapacity.FP301.Pilot0138Structural.
Require Import ZesuSsz.Generated.KeysEnsureCapacity.FP301.Pilot0150Entries.
Require Import ZesuSsz.Generated.KeysEnsureCapacity.FP301.Pilot0150Structural.
Require Import ZesuSsz.Contracts.AltFlAllocPremises.
Require Import ZesuSsz.Automation2.All.
Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith NArith.NArith.
Require Import stdpp.bitvector.definitions.
Require Import ZesuSsz.Contracts.KeysEnsureCapacityBlockEntries.
Require Import ZesuSsz.Contracts.KeysEnsureCapacitySelected.
Require Import ZesuSsz.Generated.KeysEnsureCapacity.FP301.Edges0138.
Require Import ZesuSsz.Automation2.All.
Require Import ZesuSsz.Residuals.keysEnsureCapacity.Block0138.
Local Open Scope Z_scope.
#[local] Typeclasses Transparent keysEnsureCapacitySelectedCode.

Definition DesignedEntry_800cb544
    `{!islaG Sigma} `{!threadG} (args : KeysEnsureCapacityBlockArgs) (returnAddress : Z) (K : iProp Sigma) : iProp Sigma :=
  ((ZesuSsz.Generated.KeysEnsureCapacity.FP301.Pilot0138Entries.fp_machineAt0138 (args) (returnAddress) (K)) ∗
   True)%I.
Global Instance : LithiumUnfold (@DesignedEntry_800cb544) := I.
Global Typeclasses Opaque DesignedEntry_800cb544.

Lemma DesignedBoundary_800cb544 `{!islaG Sigma} `{!threadG} (args : KeysEnsureCapacityBlockArgs) (returnAddress : Z) (K : iProp Sigma)  :
  instr_pre 0x800cb55c (ZesuSsz.Generated.KeysEnsureCapacity.FP301.Pilot0150Entries.fp_machineAt0150 (args) (returnAddress) (K))%I -∗
  instr_pre 0x80042494 (ZesuSsz.Contracts.AltFlAllocPremises.altFlAllocCallSpec)%I -∗
  keysEnsureCapacitySelectedCode -∗
  instr_body 0x800cb544
    (DesignedEntry_800cb544 args returnAddress K).
Proof.
  zesu_block2.
Qed.

Print Assumptions DesignedBoundary_800cb544.
