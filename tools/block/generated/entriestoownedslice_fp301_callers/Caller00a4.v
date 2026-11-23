Require Import ZesuSsz.Generated.EntriesToOwnedSlice.FP301.Pilot00a4Entries.
Require Import ZesuSsz.Generated.EntriesToOwnedSlice.FP301.Pilot00a4Structural.
Require Import ZesuSsz.Generated.EntriesToOwnedSlice.FP301.Pilot00acEntries.
Require Import ZesuSsz.Generated.EntriesToOwnedSlice.FP301.Pilot00acStructural.
Require Import ZesuSsz.Generated.EntriesToOwnedSlice.FP301.Pilot0108Entries.
Require Import ZesuSsz.Generated.EntriesToOwnedSlice.FP301.Pilot0108Structural.
Require Import ZesuSsz.Automation2.All.
Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith NArith.NArith.
Require Import stdpp.bitvector.definitions.
Require Import ZesuSsz.Contracts.EntriesToOwnedSliceBlockEntries.
Require Import ZesuSsz.Contracts.EntriesToOwnedSliceSelected.
Require Import ZesuSsz.Generated.EntriesToOwnedSlice.FP301.Edges00a4.
Require Import ZesuSsz.Automation2.All.
Local Open Scope Z_scope.
#[local] Typeclasses Transparent entriesToOwnedSliceSelectedCode.

Definition DesignedEntry_800d65f8
    `{!islaG Sigma} `{!threadG} (args : EntriesToOwnedSliceBlockArgs) (returnAddress : Z) (K : iProp Sigma) : iProp Sigma :=
  ((ZesuSsz.Generated.EntriesToOwnedSlice.FP301.Pilot00a4Entries.fp_machineAt00a4 (args) (returnAddress) (K)) ∗
   True)%I.
Global Instance : LithiumUnfold (@DesignedEntry_800d65f8) := I.
Global Typeclasses Opaque DesignedEntry_800d65f8.

Lemma DesignedBoundary_800d65f8 `{!islaG Sigma} `{!threadG} (args : EntriesToOwnedSliceBlockArgs) (returnAddress : Z) (K : iProp Sigma)  :
  instr_pre 0x800d6600 (ZesuSsz.Generated.EntriesToOwnedSlice.FP301.Pilot00acEntries.fp_machineAt00ac (args) (returnAddress) (K))%I -∗
  instr_pre 0x800d665c (ZesuSsz.Generated.EntriesToOwnedSlice.FP301.Pilot0108Entries.fp_machineAt0108 (args) (returnAddress) (K))%I -∗
  entriesToOwnedSliceSelectedCode -∗
  instr_body 0x800d65f8
    (DesignedEntry_800d65f8 args returnAddress K).
Proof.
  zesu_block2.
Qed.

Print Assumptions DesignedBoundary_800d65f8.
