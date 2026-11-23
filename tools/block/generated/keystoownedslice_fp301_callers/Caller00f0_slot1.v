Require Import ZesuSsz.Generated.KeysToOwnedSlice.FP301.Pilot00f0Entries.
Require Import ZesuSsz.Generated.KeysToOwnedSlice.FP301.Pilot00f0Structural.
Require Import ZesuSsz.Generated.KeysToOwnedSlice.FP301.Pilot0118Entries.
Require Import ZesuSsz.Generated.KeysToOwnedSlice.FP301.Pilot0118Structural.
Require Import ZesuSsz.Automation2.All.
Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith NArith.NArith.
Require Import stdpp.bitvector.definitions.
Require Import ZesuSsz.Contracts.KeysToOwnedSliceBlockEntries.
Require Import ZesuSsz.Contracts.KeysToOwnedSliceSelected.
Require Import ZesuSsz.Generated.KeysToOwnedSlice.FP301.Edges00f0.
Require Import ZesuSsz.Automation2.All.
Local Open Scope Z_scope.
#[local] Typeclasses Transparent keysToOwnedSliceSelectedCode.

Definition DesignedEntry_800d686c_slot1
    `{!islaG Sigma} `{!threadG} (args : KeysToOwnedSliceBlockArgs) (returnAddress : Z) (K : iProp Sigma) : iProp Sigma :=
  ((ZesuSsz.Generated.KeysToOwnedSlice.FP301.Pilot00f0Entries.fp_machineAt00f0_slot1 (args) (returnAddress) (K)) ∗
   True)%I.
Global Instance : LithiumUnfold (@DesignedEntry_800d686c_slot1) := I.
Global Typeclasses Opaque DesignedEntry_800d686c_slot1.

Lemma DesignedBoundary_800d686c_slot1 `{!islaG Sigma} `{!threadG} (args : KeysToOwnedSliceBlockArgs) (returnAddress : Z) (K : iProp Sigma)  :
  instr_pre 0x800d6894 (ZesuSsz.Generated.KeysToOwnedSlice.FP301.Pilot0118Entries.fp_machineAt0118_slot2 (args) (returnAddress) (K))%I -∗
  keysToOwnedSliceSelectedCode -∗
  instr_body 0x800d686c
    (DesignedEntry_800d686c_slot1 args returnAddress K).
Proof.
  zesu_block2.
Qed.

Print Assumptions DesignedBoundary_800d686c_slot1.
