Require Import ZesuSsz.Generated.EntriesToOwnedSlice.FP301.Pilot018cEntries.
Require Import ZesuSsz.Generated.EntriesToOwnedSlice.FP301.Pilot018cStructural.
Require Import ZesuSsz.Generated.EntriesToOwnedSlice.FP301.Pilot01a4Entries.
Require Import ZesuSsz.Generated.EntriesToOwnedSlice.FP301.Pilot01a4Structural.
Require Import ZesuSsz.Contracts.AltFlAllocPremises.
Require Import ZesuSsz.Automation2.All.
Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith NArith.NArith.
Require Import stdpp.bitvector.definitions.
Require Import ZesuSsz.Contracts.EntriesToOwnedSliceBlockEntries.
Require Import ZesuSsz.Contracts.EntriesToOwnedSliceSelected.
Require Import ZesuSsz.Generated.EntriesToOwnedSlice.FP301.Edges018c.
Require Import ZesuSsz.Automation2.All.
Require Import ZesuSsz.Residuals.entriesToOwnedSlice.Block018c.
Local Open Scope Z_scope.
#[local] Typeclasses Transparent entriesToOwnedSliceSelectedCode.

Definition DesignedEntry_800d66e0
    `{!islaG Sigma} `{!threadG} (args : EntriesToOwnedSliceBlockArgs) (returnAddress : Z) (K : iProp Sigma) : iProp Sigma :=
  ((ZesuSsz.Generated.EntriesToOwnedSlice.FP301.Pilot018cEntries.fp_machineAt018c (args) (returnAddress) (K)) ∗
   True)%I.
Global Instance : LithiumUnfold (@DesignedEntry_800d66e0) := I.
Global Typeclasses Opaque DesignedEntry_800d66e0.

Lemma DesignedBoundary_800d66e0 `{!islaG Sigma} `{!threadG} (args : EntriesToOwnedSliceBlockArgs) (returnAddress : Z) (K : iProp Sigma)  :
  instr_pre 0x800d66f8 (ZesuSsz.Generated.EntriesToOwnedSlice.FP301.Pilot01a4Entries.fp_machineAt01a4 (args) (returnAddress) (K))%I -∗
  instr_pre 0x80042494 (ZesuSsz.Contracts.AltFlAllocPremises.altFlAllocCallSpec)%I -∗
  entriesToOwnedSliceSelectedCode -∗
  instr_body 0x800d66e0
    (DesignedEntry_800d66e0 args returnAddress K).
Proof.
  zesu_block2.
Qed.

Print Assumptions DesignedBoundary_800d66e0.
