Require Import ZesuSsz.Generated.KeysEnsureCapacity.FP301.Pilot0118Entries.
Require Import ZesuSsz.Generated.KeysEnsureCapacity.FP301.Pilot0118Structural.
Require Import ZesuSsz.Generated.KeysEnsureCapacity.FP301.Pilot0124Entries.
Require Import ZesuSsz.Generated.KeysEnsureCapacity.FP301.Pilot0124Structural.
Require Import ZesuSsz.Generated.KeysEnsureCapacity.FP301.Pilot012cEntries.
Require Import ZesuSsz.Generated.KeysEnsureCapacity.FP301.Pilot012cStructural.
Require Import ZesuSsz.Automation2.All.
Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith NArith.NArith.
Require Import stdpp.bitvector.definitions.
Require Import ZesuSsz.Contracts.KeysEnsureCapacityBlockEntries.
Require Import ZesuSsz.Contracts.KeysEnsureCapacitySelected.
Require Import ZesuSsz.Generated.KeysEnsureCapacity.FP301.Edges0118.
Require Import ZesuSsz.Automation2.All.
Local Open Scope Z_scope.
#[local] Typeclasses Transparent keysEnsureCapacitySelectedCode.

Definition DesignedEntry_800cb524
    `{!islaG Sigma} `{!threadG} (args : KeysEnsureCapacityBlockArgs) (returnAddress : Z) (K : iProp Sigma) : iProp Sigma :=
  ((ZesuSsz.Generated.KeysEnsureCapacity.FP301.Pilot0118Entries.fp_machineAt0118 (args) (returnAddress) (K)) ∗
   True)%I.
Global Instance : LithiumUnfold (@DesignedEntry_800cb524) := I.
Global Typeclasses Opaque DesignedEntry_800cb524.

Lemma DesignedBoundary_800cb524 `{!islaG Sigma} `{!threadG} (args : KeysEnsureCapacityBlockArgs) (returnAddress : Z) (K : iProp Sigma)  :
  instr_pre 0x800cb530 (ZesuSsz.Generated.KeysEnsureCapacity.FP301.Pilot0124Entries.fp_machineAt0124 (args) (returnAddress) (K))%I -∗
  instr_pre 0x800cb538 (ZesuSsz.Generated.KeysEnsureCapacity.FP301.Pilot012cEntries.fp_machineAt012c (args) (returnAddress) (K))%I -∗
  keysEnsureCapacitySelectedCode -∗
  instr_body 0x800cb524
    (DesignedEntry_800cb524 args returnAddress K).
Proof.
  zesu_block2.
Qed.

Print Assumptions DesignedBoundary_800cb524.
