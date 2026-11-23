Require Import ZesuSsz.Generated.EntriesToOwnedSlice.FP301.Pilot005cEntries.
Require Import ZesuSsz.Generated.EntriesToOwnedSlice.FP301.Pilot005cStructural.
Require Import ZesuSsz.Generated.EntriesToOwnedSlice.FP301.Pilot0070Entries.
Require Import ZesuSsz.Generated.EntriesToOwnedSlice.FP301.Pilot0070Structural.
Require Import ZesuSsz.Generated.EntriesToOwnedSlice.FP301.Pilot00b0Entries.
Require Import ZesuSsz.Generated.EntriesToOwnedSlice.FP301.Pilot00b0Structural.
Require Import ZesuSsz.Automation2.All.
Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith NArith.NArith.
Require Import stdpp.bitvector.definitions.
Require Import ZesuSsz.Contracts.EntriesToOwnedSliceBlockEntries.
Require Import ZesuSsz.Contracts.EntriesToOwnedSliceSelected.
Require Import ZesuSsz.Generated.EntriesToOwnedSlice.FP301.Edges005c.
Require Import ZesuSsz.Automation2.All.
Local Open Scope Z_scope.
#[local] Typeclasses Transparent entriesToOwnedSliceSelectedCode.

Definition DesignedEntry_800d65b0
    `{!islaG Sigma} `{!threadG} (args : EntriesToOwnedSliceBlockArgs) (returnAddress : Z) (K : iProp Sigma) : iProp Sigma :=
  ((ZesuSsz.Generated.EntriesToOwnedSlice.FP301.Pilot005cEntries.fp_machineAt005c (args) (returnAddress) (K)) ∗
   True)%I.
Global Instance : LithiumUnfold (@DesignedEntry_800d65b0) := I.
Global Typeclasses Opaque DesignedEntry_800d65b0.

Lemma DesignedBoundary_800d65b0 `{!islaG Sigma} `{!threadG} (args : EntriesToOwnedSliceBlockArgs) (returnAddress : Z) (K : iProp Sigma)  :
  instr_pre 0x800d65c4 (ZesuSsz.Generated.EntriesToOwnedSlice.FP301.Pilot0070Entries.fp_machineAt0070 (args) (returnAddress) (K))%I -∗
  instr_pre 0x800d6604 (ZesuSsz.Generated.EntriesToOwnedSlice.FP301.Pilot00b0Entries.fp_machineAt00b0 (args) (returnAddress) (K))%I -∗
  entriesToOwnedSliceSelectedCode -∗
  instr_body 0x800d65b0
    (DesignedEntry_800d65b0 args returnAddress K).
Proof.
  zesu_block2.
Qed.

Print Assumptions DesignedBoundary_800d65b0.
