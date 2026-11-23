Require Import ZesuSsz.Generated.KeysToOwnedSlice.FP301.Pilot00a4Entries.
Require Import ZesuSsz.Generated.KeysToOwnedSlice.FP301.Pilot00a4Structural.
Require Import ZesuSsz.Generated.KeysToOwnedSlice.FP301.Pilot00c8Entries.
Require Import ZesuSsz.Generated.KeysToOwnedSlice.FP301.Pilot00c8Structural.
Require Import ZesuSsz.Contracts.AltFlAllocPremises.
Require Import ZesuSsz.Automation2.All.
Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith NArith.NArith.
Require Import stdpp.bitvector.definitions.
Require Import ZesuSsz.Contracts.KeysToOwnedSliceBlockEntries.
Require Import ZesuSsz.Contracts.KeysToOwnedSliceSelected.
Require Import ZesuSsz.Generated.KeysToOwnedSlice.FP301.Edges00a4.
Require Import ZesuSsz.Automation2.All.
Local Open Scope Z_scope.
#[local] Typeclasses Transparent keysToOwnedSliceSelectedCode.

Definition DesignedEntry_800d6820
    `{!islaG Sigma} `{!threadG} (args : KeysToOwnedSliceBlockArgs) (returnAddress : Z) (K : iProp Sigma) : iProp Sigma :=
  ((ZesuSsz.Generated.KeysToOwnedSlice.FP301.Pilot00a4Entries.fp_machineAt00a4 (args) (returnAddress) (K)) ∗
   True)%I.
Global Instance : LithiumUnfold (@DesignedEntry_800d6820) := I.
Global Typeclasses Opaque DesignedEntry_800d6820.

Lemma DesignedBoundary_800d6820 `{!islaG Sigma} `{!threadG} (args : KeysToOwnedSliceBlockArgs) (returnAddress : Z) (K : iProp Sigma)  :
  instr_pre 0x800d6844 (ZesuSsz.Generated.KeysToOwnedSlice.FP301.Pilot00c8Entries.fp_machineAt00c8 (args) (returnAddress) (K))%I -∗
  instr_pre 0x8004218c (ZesuSsz.Contracts.AltFlAllocPremises.altFlRemapCallSpec)%I -∗
  keysToOwnedSliceSelectedCode -∗
  instr_body 0x800d6820
    (DesignedEntry_800d6820 args returnAddress K).
Proof.
  zesu_block2.
Qed.

Print Assumptions DesignedBoundary_800d6820.
