Require Import ZesuSsz.Generated.KeysToOwnedSlice.FP301.Pilot00a0Entries.
Require Import ZesuSsz.Generated.KeysToOwnedSlice.FP301.Pilot00a0Structural.
Require Import ZesuSsz.Generated.KeysToOwnedSlice.FP301.Pilot00fcEntries.
Require Import ZesuSsz.Generated.KeysToOwnedSlice.FP301.Pilot00fcStructural.
Require Import ZesuSsz.Automation2.All.
Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith NArith.NArith.
Require Import stdpp.bitvector.definitions.
Require Import ZesuSsz.Contracts.KeysToOwnedSliceBlockEntries.
Require Import ZesuSsz.Contracts.KeysToOwnedSliceSelected.
Require Import ZesuSsz.Automation2.All.
Local Open Scope Z_scope.
#[local] Typeclasses Transparent keysToOwnedSliceSelectedCode.

Definition DesignedEntry_800d681c
    `{!islaG Sigma} `{!threadG} (args : KeysToOwnedSliceBlockArgs) (returnAddress : Z) (K : iProp Sigma) : iProp Sigma :=
  ((ZesuSsz.Generated.KeysToOwnedSlice.FP301.Pilot00a0Entries.fp_machineAt00a0 (args) (returnAddress) (K)) ∗
   True)%I.
Global Instance : LithiumUnfold (@DesignedEntry_800d681c) := I.
Global Typeclasses Opaque DesignedEntry_800d681c.

Lemma DesignedBoundary_800d681c `{!islaG Sigma} `{!threadG} (args : KeysToOwnedSliceBlockArgs) (returnAddress : Z) (K : iProp Sigma)  :
  instr_pre 0x800d6878 (ZesuSsz.Generated.KeysToOwnedSlice.FP301.Pilot00fcEntries.fp_machineAt00fc (args) (returnAddress) (K))%I -∗
  keysToOwnedSliceSelectedCode -∗
  instr_body 0x800d681c
    (DesignedEntry_800d681c args returnAddress K).
Proof.
  zesu_block2.
Qed.

Print Assumptions DesignedBoundary_800d681c.
