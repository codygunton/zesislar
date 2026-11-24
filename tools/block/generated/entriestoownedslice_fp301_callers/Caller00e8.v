Require Import ZesuSsz.Generated.EntriesToOwnedSlice.FP301.Pilot00e8Entries.
Require Import ZesuSsz.Generated.EntriesToOwnedSlice.FP301.Pilot00e8Structural.
Require Import ZesuSsz.Generated.EntriesToOwnedSlice.FP301.Pilot0108Entries.
Require Import ZesuSsz.Generated.EntriesToOwnedSlice.FP301.Pilot0108Structural.
Require Import ZesuSsz.Generated.EntriesToOwnedSlice.FP301.Pilot012cEntries.
Require Import ZesuSsz.Generated.EntriesToOwnedSlice.FP301.Pilot012cStructural.
Require Import ZesuSsz.Automation2.All.
Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith NArith.NArith.
Require Import stdpp.bitvector.definitions.
Require Import ZesuSsz.Contracts.EntriesToOwnedSliceBlockEntries.
Require Import ZesuSsz.Contracts.EntriesToOwnedSliceSelected.
Require Import ZesuSsz.Automation2.All.
Local Open Scope Z_scope.
#[local] Typeclasses Transparent entriesToOwnedSliceSelectedCode.

Definition DesignedEntry_800d663c
    `{!islaG Sigma} `{!threadG} (args : EntriesToOwnedSliceBlockArgs) (returnAddress : Z) (K : iProp Sigma) : iProp Sigma :=
  ((ZesuSsz.Generated.EntriesToOwnedSlice.FP301.Pilot00e8Entries.fp_machineAt00e8 (args) (returnAddress) (K)) ∗
   True)%I.
Global Instance : LithiumUnfold (@DesignedEntry_800d663c) := I.
Global Typeclasses Opaque DesignedEntry_800d663c.

Lemma DesignedBoundary_800d663c `{!islaG Sigma} `{!threadG} (args : EntriesToOwnedSliceBlockArgs) (returnAddress : Z) (K : iProp Sigma)  :
  instr_pre 0x800d665c (ZesuSsz.Generated.EntriesToOwnedSlice.FP301.Pilot0108Entries.fp_machineAt0108 (args) (returnAddress) (K))%I -∗
  instr_pre 0x800d6680 (ZesuSsz.Generated.EntriesToOwnedSlice.FP301.Pilot012cEntries.fp_machineAt012c (args) (returnAddress) (K))%I -∗
  entriesToOwnedSliceSelectedCode -∗
  instr_body 0x800d663c
    (DesignedEntry_800d663c args returnAddress K).
Proof.
  zesu_block2.
Qed.

Print Assumptions DesignedBoundary_800d663c.
