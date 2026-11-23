Require Import ZesuSsz.Generated.EntriesToOwnedSlice.FP301.Pilot01c0Entries.
Require Import ZesuSsz.Generated.EntriesToOwnedSlice.FP301.Pilot01c0Structural.
Require Import ZesuSsz.Generated.EntriesToOwnedSlice.FP301.Pilot01c8Entries.
Require Import ZesuSsz.Generated.EntriesToOwnedSlice.FP301.Pilot01c8Structural.
Require Import ZesuSsz.Generated.EntriesToOwnedSlice.FP301.Pilot01f0Entries.
Require Import ZesuSsz.Generated.EntriesToOwnedSlice.FP301.Pilot01f0Structural.
Require Import ZesuSsz.Automation2.All.
Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith NArith.NArith.
Require Import stdpp.bitvector.definitions.
Require Import ZesuSsz.Contracts.EntriesToOwnedSliceBlockEntries.
Require Import ZesuSsz.Contracts.EntriesToOwnedSliceSelected.
Require Import ZesuSsz.Generated.EntriesToOwnedSlice.FP301.Edges01c0.
Require Import ZesuSsz.Automation2.All.
Local Open Scope Z_scope.
#[local] Typeclasses Transparent entriesToOwnedSliceSelectedCode.

Definition DesignedEntry_800d6714
    `{!islaG Sigma} `{!threadG} (args : EntriesToOwnedSliceBlockArgs) (returnAddress : Z) (K : iProp Sigma) : iProp Sigma :=
  ((ZesuSsz.Generated.EntriesToOwnedSlice.FP301.Pilot01c0Entries.fp_machineAt01c0 (args) (returnAddress) (K)) ∗
   True)%I.
Global Instance : LithiumUnfold (@DesignedEntry_800d6714) := I.
Global Typeclasses Opaque DesignedEntry_800d6714.

Lemma DesignedBoundary_800d6714 `{!islaG Sigma} `{!threadG} (args : EntriesToOwnedSliceBlockArgs) (returnAddress : Z) (K : iProp Sigma)  :
  instr_pre 0x800d671c (ZesuSsz.Generated.EntriesToOwnedSlice.FP301.Pilot01c8Entries.fp_machineAt01c8 (args) (returnAddress) (K))%I -∗
  instr_pre 0x800d6744 (ZesuSsz.Generated.EntriesToOwnedSlice.FP301.Pilot01f0Entries.fp_machineAt01f0 (args) (returnAddress) (K))%I -∗
  entriesToOwnedSliceSelectedCode -∗
  instr_body 0x800d6714
    (DesignedEntry_800d6714 args returnAddress K).
Proof.
  zesu_block2.
Qed.

Print Assumptions DesignedBoundary_800d6714.
