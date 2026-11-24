Require Import ZesuSsz.Generated.KeysEnsureCapacity.FP301.Pilot003cEntries.
Require Import ZesuSsz.Generated.KeysEnsureCapacity.FP301.Pilot003cStructural.
Require Import ZesuSsz.Generated.KeysEnsureCapacity.FP301.Pilot0068Entries.
Require Import ZesuSsz.Generated.KeysEnsureCapacity.FP301.Pilot0068Structural.
Require Import ZesuSsz.Generated.KeysEnsureCapacity.FP301.Pilot0074Entries.
Require Import ZesuSsz.Generated.KeysEnsureCapacity.FP301.Pilot0074Structural.
Require Import ZesuSsz.Automation2.All.
Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith NArith.NArith.
Require Import stdpp.bitvector.definitions.
Require Import ZesuSsz.Contracts.KeysEnsureCapacityBlockEntries.
Require Import ZesuSsz.Contracts.KeysEnsureCapacitySelected.
Require Import ZesuSsz.Generated.KeysEnsureCapacity.FP301.Edges003c.
Require Import ZesuSsz.Automation2.All.
Require Import ZesuSsz.Residuals.keysEnsureCapacity.Block003c.
Local Open Scope Z_scope.
#[local] Typeclasses Transparent keysEnsureCapacitySelectedCode.

Definition DesignedEntry_800cb448
    `{!islaG Sigma} `{!threadG} (args : KeysEnsureCapacityBlockArgs) (returnAddress : Z) (K : iProp Sigma) : iProp Sigma :=
  ((ZesuSsz.Generated.KeysEnsureCapacity.FP301.Pilot003cEntries.fp_machineAt003c (args) (returnAddress) (K)) ∗
   True)%I.
Global Instance : LithiumUnfold (@DesignedEntry_800cb448) := I.
Global Typeclasses Opaque DesignedEntry_800cb448.

Lemma DesignedBoundary_800cb448 `{!islaG Sigma} `{!threadG} (args : KeysEnsureCapacityBlockArgs) (returnAddress : Z) (K : iProp Sigma)  :
  instr_pre 0x800cb474 (ZesuSsz.Generated.KeysEnsureCapacity.FP301.Pilot0068Entries.fp_machineAt0068 (args) (returnAddress) (K))%I -∗
  instr_pre 0x800cb480 (ZesuSsz.Generated.KeysEnsureCapacity.FP301.Pilot0074Entries.fp_machineAt0074 (args) (returnAddress) (K))%I -∗
  keysEnsureCapacitySelectedCode -∗
  instr_body 0x800cb448
    (DesignedEntry_800cb448 args returnAddress K).
Proof.
  zesu_block2.
Qed.

Print Assumptions DesignedBoundary_800cb448.
