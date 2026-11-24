Require Import ZesuSsz.Generated.KeysEnsureCapacity.FP301.Pilot015cEntries.
Require Import ZesuSsz.Generated.KeysEnsureCapacity.FP301.Pilot015cStructural.
Require Import ZesuSsz.Generated.KeysEnsureCapacity.FP301.Pilot0164Entries.
Require Import ZesuSsz.Generated.KeysEnsureCapacity.FP301.Pilot0164Structural.
Require Import ZesuSsz.Automation2.All.
Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith NArith.NArith.
Require Import stdpp.bitvector.definitions.
Require Import ZesuSsz.Contracts.KeysEnsureCapacityBlockEntries.
Require Import ZesuSsz.Contracts.KeysEnsureCapacitySelected.
Require Import ZesuSsz.Automation2.All.
Local Open Scope Z_scope.
#[local] Typeclasses Transparent keysEnsureCapacitySelectedCode.

Definition DesignedEntry_800cb568
    `{!islaG Sigma} `{!threadG} (args : KeysEnsureCapacityBlockArgs) (returnAddress : Z) (K : iProp Sigma) : iProp Sigma :=
  ((ZesuSsz.Generated.KeysEnsureCapacity.FP301.Pilot015cEntries.fp_machineAt015c (args) (returnAddress) (K)) ∗
   True)%I.
Global Instance : LithiumUnfold (@DesignedEntry_800cb568) := I.
Global Typeclasses Opaque DesignedEntry_800cb568.

Lemma DesignedBoundary_800cb568 `{!islaG Sigma} `{!threadG} (args : KeysEnsureCapacityBlockArgs) (returnAddress : Z) (K : iProp Sigma)  :
  instr_pre 0x800cb570 (ZesuSsz.Generated.KeysEnsureCapacity.FP301.Pilot0164Entries.fp_machineAt0164 (args) (returnAddress) (K))%I -∗
  keysEnsureCapacitySelectedCode -∗
  instr_body 0x800cb568
    (DesignedEntry_800cb568 args returnAddress K).
Proof.
  zesu_block2.
Qed.

Print Assumptions DesignedBoundary_800cb568.
