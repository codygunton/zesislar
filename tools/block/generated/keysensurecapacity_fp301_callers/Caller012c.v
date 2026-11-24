Require Import ZesuSsz.Generated.KeysEnsureCapacity.FP301.Pilot012cEntries.
Require Import ZesuSsz.Generated.KeysEnsureCapacity.FP301.Pilot012cStructural.
Require Import ZesuSsz.Generated.KeysEnsureCapacity.FP301.Pilot0138Entries.
Require Import ZesuSsz.Generated.KeysEnsureCapacity.FP301.Pilot0138Structural.
Require Import ZesuSsz.Generated.KeysEnsureCapacity.FP301.Pilot015cEntries.
Require Import ZesuSsz.Generated.KeysEnsureCapacity.FP301.Pilot015cStructural.
Require Import ZesuSsz.Automation2.All.
Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith NArith.NArith.
Require Import stdpp.bitvector.definitions.
Require Import ZesuSsz.Contracts.KeysEnsureCapacityBlockEntries.
Require Import ZesuSsz.Contracts.KeysEnsureCapacitySelected.
Require Import ZesuSsz.Generated.KeysEnsureCapacity.FP301.Edges012c.
Require Import ZesuSsz.Automation2.All.
Require Import ZesuSsz.Residuals.keysEnsureCapacity.Block012c.
Local Open Scope Z_scope.
#[local] Typeclasses Transparent keysEnsureCapacitySelectedCode.

Definition DesignedEntry_800cb538
    `{!islaG Sigma} `{!threadG} (args : KeysEnsureCapacityBlockArgs) (returnAddress : Z) (K : iProp Sigma) : iProp Sigma :=
  ((ZesuSsz.Generated.KeysEnsureCapacity.FP301.Pilot012cEntries.fp_machineAt012c (args) (returnAddress) (K)) ∗
   True)%I.
Global Instance : LithiumUnfold (@DesignedEntry_800cb538) := I.
Global Typeclasses Opaque DesignedEntry_800cb538.

Lemma DesignedBoundary_800cb538 `{!islaG Sigma} `{!threadG} (args : KeysEnsureCapacityBlockArgs) (returnAddress : Z) (K : iProp Sigma)  :
  instr_pre 0x800cb544 (ZesuSsz.Generated.KeysEnsureCapacity.FP301.Pilot0138Entries.fp_machineAt0138 (args) (returnAddress) (K))%I -∗
  instr_pre 0x800cb568 (ZesuSsz.Generated.KeysEnsureCapacity.FP301.Pilot015cEntries.fp_machineAt015c (args) (returnAddress) (K))%I -∗
  keysEnsureCapacitySelectedCode -∗
  instr_body 0x800cb538
    (DesignedEntry_800cb538 args returnAddress K).
Proof.
  zesu_block2.
Qed.

Print Assumptions DesignedBoundary_800cb538.
