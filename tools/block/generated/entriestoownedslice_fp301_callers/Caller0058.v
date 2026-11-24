Require Import ZesuSsz.Generated.EntriesToOwnedSlice.FP301.Pilot0058Entries.
Require Import ZesuSsz.Generated.EntriesToOwnedSlice.FP301.Pilot0058Structural.
Require Import ZesuSsz.Generated.EntriesToOwnedSlice.FP301.Pilot005cEntries.
Require Import ZesuSsz.Generated.EntriesToOwnedSlice.FP301.Pilot005cStructural.
Require Import ZesuSsz.Generated.EntriesToOwnedSlice.FP301.Pilot0070Entries.
Require Import ZesuSsz.Generated.EntriesToOwnedSlice.FP301.Pilot0070Structural.
Require Import ZesuSsz.Automation2.All.
Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith NArith.NArith.
Require Import stdpp.bitvector.definitions.
Require Import ZesuSsz.Contracts.EntriesToOwnedSliceBlockEntries.
Require Import ZesuSsz.Contracts.EntriesToOwnedSliceSelected.
Require Import ZesuSsz.Generated.EntriesToOwnedSlice.FP301.Edges0058.
Require Import ZesuSsz.Automation2.All.
Require Import ZesuSsz.Residuals.entriesToOwnedSlice.Block0058.
Local Open Scope Z_scope.
#[local] Typeclasses Transparent entriesToOwnedSliceSelectedCode.

Definition DesignedEntry_800d65ac
    `{!islaG Sigma} `{!threadG} (args : EntriesToOwnedSliceBlockArgs) (returnAddress : Z) (K : iProp Sigma) : iProp Sigma :=
  ((ZesuSsz.Generated.EntriesToOwnedSlice.FP301.Pilot0058Entries.fp_machineAt0058 (args) (returnAddress) (K)) ∗
   True)%I.
Global Instance : LithiumUnfold (@DesignedEntry_800d65ac) := I.
Global Typeclasses Opaque DesignedEntry_800d65ac.

Lemma DesignedBoundary_800d65ac `{!islaG Sigma} `{!threadG} (args : EntriesToOwnedSliceBlockArgs) (returnAddress : Z) (K : iProp Sigma)  :
  instr_pre 0x800d65b0 (ZesuSsz.Generated.EntriesToOwnedSlice.FP301.Pilot005cEntries.fp_machineAt005c (args) (returnAddress) (K))%I -∗
  instr_pre 0x800d65c4 (ZesuSsz.Generated.EntriesToOwnedSlice.FP301.Pilot0070Entries.fp_machineAt0070 (args) (returnAddress) (K))%I -∗
  entriesToOwnedSliceSelectedCode -∗
  instr_body 0x800d65ac
    (DesignedEntry_800d65ac args returnAddress K).
Proof.
  zesu_block2.
Qed.

Print Assumptions DesignedBoundary_800d65ac.
