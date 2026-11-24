Require Import ZesuSsz.Generated.EntriesToOwnedSlice.FP301.Pilot0000Entries.
Require Import ZesuSsz.Generated.EntriesToOwnedSlice.FP301.Pilot0000Structural.
Require Import ZesuSsz.Generated.EntriesToOwnedSlice.FP301.Pilot0058Entries.
Require Import ZesuSsz.Generated.EntriesToOwnedSlice.FP301.Pilot0058Structural.
Require Import ZesuSsz.Generated.EntriesToOwnedSlice.FP301.Pilot007cEntries.
Require Import ZesuSsz.Generated.EntriesToOwnedSlice.FP301.Pilot007cStructural.
Require Import ZesuSsz.Automation2.All.
Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith NArith.NArith.
Require Import stdpp.bitvector.definitions.
Require Import ZesuSsz.Contracts.EntriesToOwnedSliceBlockEntries.
Require Import ZesuSsz.Contracts.EntriesToOwnedSliceSelected.
Require Import ZesuSsz.Generated.EntriesToOwnedSlice.FP301.Edges0000.
Require Import ZesuSsz.Automation2.All.
Require Import ZesuSsz.Residuals.entriesToOwnedSlice.Block0000.
Local Open Scope Z_scope.
#[local] Typeclasses Transparent entriesToOwnedSliceSelectedCode.

Definition DesignedEntry_800d6554
    `{!islaG Sigma} `{!threadG} (args : EntriesToOwnedSliceBlockArgs) (returnAddress : Z) (K : iProp Sigma) : iProp Sigma :=
  ((ZesuSsz.Generated.EntriesToOwnedSlice.FP301.Pilot0000Entries.fp_machineAt0000 (args) (returnAddress) (K)) ∗
   True)%I.
Global Instance : LithiumUnfold (@DesignedEntry_800d6554) := I.
Global Typeclasses Opaque DesignedEntry_800d6554.

Lemma DesignedBoundary_800d6554 `{!islaG Sigma} `{!threadG} (args : EntriesToOwnedSliceBlockArgs) (returnAddress : Z) (K : iProp Sigma)  :
  instr_pre 0x800d65ac (ZesuSsz.Generated.EntriesToOwnedSlice.FP301.Pilot0058Entries.fp_machineAt0058 (args) (returnAddress) (K))%I -∗
  instr_pre 0x800d65d0 (ZesuSsz.Generated.EntriesToOwnedSlice.FP301.Pilot007cEntries.fp_machineAt007c (args) (returnAddress) (K))%I -∗
  entriesToOwnedSliceSelectedCode -∗
  instr_body 0x800d6554
    (DesignedEntry_800d6554 args returnAddress K).
Proof.
  zesu_block2.
Qed.

Print Assumptions DesignedBoundary_800d6554.
