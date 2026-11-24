Require Import ZesuSsz.Generated.KeysEnsureCapacity.FP301.Pilot019cEntries.
Require Import ZesuSsz.Generated.KeysEnsureCapacity.FP301.Pilot019cStructural.
Require Import ZesuSsz.Generated.KeysEnsureCapacity.FP301.Pilot008cEntries.
Require Import ZesuSsz.Generated.KeysEnsureCapacity.FP301.Pilot008cStructural.
Require Import ZesuSsz.Automation2.All.
Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith NArith.NArith.
Require Import stdpp.bitvector.definitions.
Require Import ZesuSsz.Contracts.KeysEnsureCapacityBlockEntries.
Require Import ZesuSsz.Contracts.KeysEnsureCapacitySelected.
Require Import ZesuSsz.Generated.KeysEnsureCapacity.FP301.Edges019c.
Require Import ZesuSsz.Automation2.All.
Local Open Scope Z_scope.
#[local] Typeclasses Transparent keysEnsureCapacitySelectedCode.

Definition DesignedEntry_800cb5a8
    `{!islaG Sigma} `{!threadG} (args : KeysEnsureCapacityBlockArgs) (returnAddress : Z) (K : iProp Sigma) : iProp Sigma :=
  ((ZesuSsz.Generated.KeysEnsureCapacity.FP301.Pilot019cEntries.fp_machineAt019c (args) (returnAddress) (K)) ∗
   True)%I.
Global Instance : LithiumUnfold (@DesignedEntry_800cb5a8) := I.
Global Typeclasses Opaque DesignedEntry_800cb5a8.

Lemma DesignedBoundary_800cb5a8 `{!islaG Sigma} `{!threadG} (args : KeysEnsureCapacityBlockArgs) (returnAddress : Z) (K : iProp Sigma)  :
  instr_pre 0x800cb498 (ZesuSsz.Generated.KeysEnsureCapacity.FP301.Pilot008cEntries.fp_machineAt008c_slot2 (args) (returnAddress) (K))%I -∗
  keysEnsureCapacitySelectedCode -∗
  instr_body 0x800cb5a8
    (DesignedEntry_800cb5a8 args returnAddress K).
Proof.
  zesu_block2.
Qed.

Print Assumptions DesignedBoundary_800cb5a8.
