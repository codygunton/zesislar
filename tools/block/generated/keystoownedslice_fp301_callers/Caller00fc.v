Require Import ZesuSsz.Generated.KeysToOwnedSlice.FP301.Pilot00fcEntries.
Require Import ZesuSsz.Generated.KeysToOwnedSlice.FP301.Pilot00fcStructural.
Require Import ZesuSsz.Generated.KeysToOwnedSlice.FP301.Pilot0110Entries.
Require Import ZesuSsz.Generated.KeysToOwnedSlice.FP301.Pilot0110Structural.
Require Import ZesuSsz.Generated.KeysToOwnedSlice.FP301.Pilot0148Entries.
Require Import ZesuSsz.Generated.KeysToOwnedSlice.FP301.Pilot0148Structural.
Require Import ZesuSsz.Automation2.All.
Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith NArith.NArith.
Require Import stdpp.bitvector.definitions.
Require Import ZesuSsz.Contracts.KeysToOwnedSliceBlockEntries.
Require Import ZesuSsz.Contracts.KeysToOwnedSliceSelected.
Require Import ZesuSsz.Generated.KeysToOwnedSlice.FP301.Edges00fc.
Require Import ZesuSsz.Automation2.All.
Local Open Scope Z_scope.
#[local] Typeclasses Transparent keysToOwnedSliceSelectedCode.

Definition DesignedEntry_800d6878
    `{!islaG Sigma} `{!threadG} (args : KeysToOwnedSliceBlockArgs) (returnAddress : Z) (K : iProp Sigma) : iProp Sigma :=
  ((ZesuSsz.Generated.KeysToOwnedSlice.FP301.Pilot00fcEntries.fp_machineAt00fc (args) (returnAddress) (K)) ∗
   True)%I.
Global Instance : LithiumUnfold (@DesignedEntry_800d6878) := I.
Global Typeclasses Opaque DesignedEntry_800d6878.

Lemma DesignedBoundary_800d6878 `{!islaG Sigma} `{!threadG} (args : KeysToOwnedSliceBlockArgs) (returnAddress : Z) (K : iProp Sigma)  :
  instr_pre 0x800d688c (ZesuSsz.Generated.KeysToOwnedSlice.FP301.Pilot0110Entries.fp_machineAt0110 (args) (returnAddress) (K))%I -∗
  instr_pre 0x800d68c4 (ZesuSsz.Generated.KeysToOwnedSlice.FP301.Pilot0148Entries.fp_machineAt0148 (args) (returnAddress) (K))%I -∗
  keysToOwnedSliceSelectedCode -∗
  instr_body 0x800d6878
    (DesignedEntry_800d6878 args returnAddress K).
Proof.
  zesu_block2.
Qed.

Print Assumptions DesignedBoundary_800d6878.
