Require Import ZesuSsz.Generated.EntriesToOwnedSlice.FP301.Pilot0080Entries.
Require Import ZesuSsz.Generated.EntriesToOwnedSlice.FP301.Pilot0080Structural.
Require Import ZesuSsz.Generated.EntriesToOwnedSlice.FP301.Pilot00a4Entries.
Require Import ZesuSsz.Generated.EntriesToOwnedSlice.FP301.Pilot00a4Structural.
Require Import ZesuSsz.Contracts.AltFlAllocPremises.
Require Import ZesuSsz.Automation2.All.
Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith NArith.NArith.
Require Import stdpp.bitvector.definitions.
Require Import ZesuSsz.Contracts.EntriesToOwnedSliceBlockEntries.
Require Import ZesuSsz.Contracts.EntriesToOwnedSliceSelected.
Require Import ZesuSsz.Generated.EntriesToOwnedSlice.FP301.Edges0080.
Require Import ZesuSsz.Automation2.All.
Local Open Scope Z_scope.
#[local] Typeclasses Transparent entriesToOwnedSliceSelectedCode.

Definition DesignedEntry_800d65d4
    `{!islaG Sigma} `{!threadG} (args : EntriesToOwnedSliceBlockArgs) (returnAddress : Z) (K : iProp Sigma) : iProp Sigma :=
  ((ZesuSsz.Generated.EntriesToOwnedSlice.FP301.Pilot0080Entries.fp_machineAt0080 (args) (returnAddress) (K)) ∗
   True)%I.
Global Instance : LithiumUnfold (@DesignedEntry_800d65d4) := I.
Global Typeclasses Opaque DesignedEntry_800d65d4.

Lemma DesignedBoundary_800d65d4 `{!islaG Sigma} `{!threadG} (args : EntriesToOwnedSliceBlockArgs) (returnAddress : Z) (K : iProp Sigma)  :
  instr_pre 0x800d65f8 (ZesuSsz.Generated.EntriesToOwnedSlice.FP301.Pilot00a4Entries.fp_machineAt00a4 (args) (returnAddress) (K))%I -∗
  instr_pre 0x80041f38 (ZesuSsz.Contracts.AltFlAllocPremises.altFlFreeCallSpec)%I -∗
  entriesToOwnedSliceSelectedCode -∗
  instr_body 0x800d65d4
    (DesignedEntry_800d65d4 args returnAddress K).
Proof.
  zesu_block2.
Qed.

Print Assumptions DesignedBoundary_800d65d4.
