Require Import ZesuSsz.Generated.KeysEnsureCapacity.FP301.Pilot0080Entries.
Require Import ZesuSsz.Generated.KeysEnsureCapacity.FP301.Pilot0080Structural.
Require Import ZesuSsz.Generated.KeysEnsureCapacity.FP301.Pilot0088Entries.
Require Import ZesuSsz.Generated.KeysEnsureCapacity.FP301.Pilot0088Structural.
Require Import ZesuSsz.Automation2.All.
Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith NArith.NArith.
Require Import stdpp.bitvector.definitions.
Require Import ZesuSsz.Contracts.KeysEnsureCapacityBlockEntries.
Require Import ZesuSsz.Contracts.KeysEnsureCapacitySelected.
Require Import ZesuSsz.Automation2.All.
Local Open Scope Z_scope.
#[local] Typeclasses Transparent keysEnsureCapacitySelectedCode.

Definition DesignedEntry_800cb48c
    `{!islaG Sigma} `{!threadG} (args : KeysEnsureCapacityBlockArgs) (returnAddress : Z) (K : iProp Sigma) : iProp Sigma :=
  ((ZesuSsz.Generated.KeysEnsureCapacity.FP301.Pilot0080Entries.fp_machineAt0080 (args) (returnAddress) (K)) ∗
   True)%I.
Global Instance : LithiumUnfold (@DesignedEntry_800cb48c) := I.
Global Typeclasses Opaque DesignedEntry_800cb48c.

Lemma DesignedBoundary_800cb48c `{!islaG Sigma} `{!threadG} (args : KeysEnsureCapacityBlockArgs) (returnAddress : Z) (K : iProp Sigma)  :
  instr_pre 0x800cb494 (ZesuSsz.Generated.KeysEnsureCapacity.FP301.Pilot0088Entries.fp_machineAt0088 (args) (returnAddress) (K))%I -∗
  keysEnsureCapacitySelectedCode -∗
  instr_body 0x800cb48c
    (DesignedEntry_800cb48c args returnAddress K).
Proof.
  zesu_block2.
Qed.

Print Assumptions DesignedBoundary_800cb48c.
