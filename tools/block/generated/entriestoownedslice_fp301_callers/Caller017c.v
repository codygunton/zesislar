Require Import ZesuSsz.Generated.EntriesToOwnedSlice.FP301.Pilot017cEntries.
Require Import ZesuSsz.Generated.EntriesToOwnedSlice.FP301.Pilot017cStructural.
Require Import ZesuSsz.Generated.EntriesToOwnedSlice.FP301.Pilot018cEntries.
Require Import ZesuSsz.Generated.EntriesToOwnedSlice.FP301.Pilot018cStructural.
Require Import ZesuSsz.Generated.EntriesToOwnedSlice.FP301.Pilot0204Entries.
Require Import ZesuSsz.Generated.EntriesToOwnedSlice.FP301.Pilot0204Structural.
Require Import ZesuSsz.Automation2.All.
Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith NArith.NArith.
Require Import stdpp.bitvector.definitions.
Require Import ZesuSsz.Contracts.EntriesToOwnedSliceBlockEntries.
Require Import ZesuSsz.Contracts.EntriesToOwnedSliceSelected.
Require Import ZesuSsz.Generated.EntriesToOwnedSlice.FP301.Edges017c.
Require Import ZesuSsz.Automation2.All.
Require Import ZesuSsz.Residuals.entriesToOwnedSlice.Block017c.
Local Open Scope Z_scope.
#[local] Typeclasses Transparent entriesToOwnedSliceSelectedCode.

Definition DesignedEntry_800d66d0
    `{!islaG Sigma} `{!threadG} (args : EntriesToOwnedSliceBlockArgs) (returnAddress : Z) (K : iProp Sigma) : iProp Sigma :=
  ((ZesuSsz.Generated.EntriesToOwnedSlice.FP301.Pilot017cEntries.fp_machineAt017c (args) (returnAddress) (K)) ∗
   True)%I.
Global Instance : LithiumUnfold (@DesignedEntry_800d66d0) := I.
Global Typeclasses Opaque DesignedEntry_800d66d0.

Lemma DesignedBoundary_800d66d0 `{!islaG Sigma} `{!threadG} (args : EntriesToOwnedSliceBlockArgs) (returnAddress : Z) (K : iProp Sigma)  :
  instr_pre 0x800d66e0 (ZesuSsz.Generated.EntriesToOwnedSlice.FP301.Pilot018cEntries.fp_machineAt018c (args) (returnAddress) (K))%I -∗
  instr_pre 0x800d6758 (ZesuSsz.Generated.EntriesToOwnedSlice.FP301.Pilot0204Entries.fp_machineAt0204 (args) (returnAddress) (K))%I -∗
  entriesToOwnedSliceSelectedCode -∗
  instr_body 0x800d66d0
    (DesignedEntry_800d66d0 args returnAddress K).
Proof.
  zesu_block2.
Qed.

Print Assumptions DesignedBoundary_800d66d0.
