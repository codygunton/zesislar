Require Import ZesuSsz.Generated.KeysToOwnedSlice.FP301.Pilot0058Entries.
Require Import ZesuSsz.Generated.KeysToOwnedSlice.FP301.Pilot0058Structural.
Require Import ZesuSsz.Generated.KeysToOwnedSlice.FP301.Pilot005cEntries.
Require Import ZesuSsz.Generated.KeysToOwnedSlice.FP301.Pilot005cStructural.
Require Import ZesuSsz.Generated.KeysToOwnedSlice.FP301.Pilot006cEntries.
Require Import ZesuSsz.Generated.KeysToOwnedSlice.FP301.Pilot006cStructural.
Require Import ZesuSsz.Automation2.All.
Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith NArith.NArith.
Require Import stdpp.bitvector.definitions.
Require Import ZesuSsz.Contracts.KeysToOwnedSliceBlockEntries.
Require Import ZesuSsz.Contracts.KeysToOwnedSliceSelected.
Require Import ZesuSsz.Generated.KeysToOwnedSlice.FP301.Edges0058.
Require Import ZesuSsz.Automation2.All.
Local Open Scope Z_scope.
#[local] Typeclasses Transparent keysToOwnedSliceSelectedCode.

Definition DesignedEntry_800d67d4
    `{!islaG Sigma} `{!threadG} (args : KeysToOwnedSliceBlockArgs) (returnAddress : Z) (K : iProp Sigma) : iProp Sigma :=
  ((ZesuSsz.Generated.KeysToOwnedSlice.FP301.Pilot0058Entries.fp_machineAt0058 (args) (returnAddress) (K)) ∗
   True)%I.
Global Instance : LithiumUnfold (@DesignedEntry_800d67d4) := I.
Global Typeclasses Opaque DesignedEntry_800d67d4.

Lemma DesignedBoundary_800d67d4 `{!islaG Sigma} `{!threadG} (args : KeysToOwnedSliceBlockArgs) (returnAddress : Z) (K : iProp Sigma)  :
  instr_pre 0x800d67d8 (ZesuSsz.Generated.KeysToOwnedSlice.FP301.Pilot005cEntries.fp_machineAt005c (args) (returnAddress) (K))%I -∗
  instr_pre 0x800d67e8 (ZesuSsz.Generated.KeysToOwnedSlice.FP301.Pilot006cEntries.fp_machineAt006c (args) (returnAddress) (K))%I -∗
  keysToOwnedSliceSelectedCode -∗
  instr_body 0x800d67d4
    (DesignedEntry_800d67d4 args returnAddress K).
Proof.
  zesu_block2.
Qed.

Print Assumptions DesignedBoundary_800d67d4.
