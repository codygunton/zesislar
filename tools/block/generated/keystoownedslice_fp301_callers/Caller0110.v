Require Import ZesuSsz.Generated.KeysToOwnedSlice.FP301.Pilot0110Entries.
Require Import ZesuSsz.Generated.KeysToOwnedSlice.FP301.Pilot0110Structural.
Require Import ZesuSsz.Generated.KeysToOwnedSlice.FP301.Pilot0118Entries.
Require Import ZesuSsz.Generated.KeysToOwnedSlice.FP301.Pilot0118Structural.
Require Import ZesuSsz.Automation2.All.
Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith NArith.NArith.
Require Import stdpp.bitvector.definitions.
Require Import ZesuSsz.Contracts.KeysToOwnedSliceBlockEntries.
Require Import ZesuSsz.Contracts.KeysToOwnedSliceSelected.
Require Import ZesuSsz.Generated.KeysToOwnedSlice.FP301.Edges0110.
Require Import ZesuSsz.Automation2.All.
Local Open Scope Z_scope.
#[local] Typeclasses Transparent keysToOwnedSliceSelectedCode.

Definition DesignedEntry_800d688c
    `{!islaG Sigma} `{!threadG} (args : KeysToOwnedSliceBlockArgs) (returnAddress : Z) (K : iProp Sigma) : iProp Sigma :=
  ((ZesuSsz.Generated.KeysToOwnedSlice.FP301.Pilot0110Entries.fp_machineAt0110 (args) (returnAddress) (K)) ∗
   True)%I.
Global Instance : LithiumUnfold (@DesignedEntry_800d688c) := I.
Global Typeclasses Opaque DesignedEntry_800d688c.

Lemma DesignedBoundary_800d688c `{!islaG Sigma} `{!threadG} (args : KeysToOwnedSliceBlockArgs) (returnAddress : Z) (K : iProp Sigma)  :
  instr_pre 0x800d6894 (ZesuSsz.Generated.KeysToOwnedSlice.FP301.Pilot0118Entries.fp_machineAt0118_slot0 (args) (returnAddress) (K))%I -∗
  keysToOwnedSliceSelectedCode -∗
  instr_body 0x800d688c
    (DesignedEntry_800d688c args returnAddress K).
Proof.
  zesu_block2.
Qed.

Print Assumptions DesignedBoundary_800d688c.
