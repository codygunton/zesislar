Require Import ZesuSsz.Generated.EntriesToOwnedSlice.FP301.Pilot00e4Entries.
Require Import ZesuSsz.Generated.EntriesToOwnedSlice.FP301.Pilot00e4Structural.
Require Import ZesuSsz.Generated.EntriesToOwnedSlice.FP301.Pilot00e8Entries.
Require Import ZesuSsz.Generated.EntriesToOwnedSlice.FP301.Pilot00e8Structural.
Require Import ZesuSsz.Generated.EntriesToOwnedSlice.FP301.Pilot0128Entries.
Require Import ZesuSsz.Generated.EntriesToOwnedSlice.FP301.Pilot0128Structural.
Require Import ZesuSsz.Automation2.All.
Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith NArith.NArith.
Require Import stdpp.bitvector.definitions.
Require Import ZesuSsz.Contracts.EntriesToOwnedSliceBlockEntries.
Require Import ZesuSsz.Contracts.EntriesToOwnedSliceSelected.
Require Import ZesuSsz.Generated.EntriesToOwnedSlice.FP301.Edges00e4.
Require Import ZesuSsz.Automation2.All.
Local Open Scope Z_scope.
#[local] Typeclasses Transparent entriesToOwnedSliceSelectedCode.

Definition DesignedEntry_800d6638
    `{!islaG Sigma} `{!threadG} (args : EntriesToOwnedSliceBlockArgs) (returnAddress : Z) (K : iProp Sigma) : iProp Sigma :=
  ((ZesuSsz.Generated.EntriesToOwnedSlice.FP301.Pilot00e4Entries.fp_machineAt00e4 (args) (returnAddress) (K)) ∗
   True)%I.
Global Instance : LithiumUnfold (@DesignedEntry_800d6638) := I.
Global Typeclasses Opaque DesignedEntry_800d6638.

Lemma DesignedBoundary_800d6638 `{!islaG Sigma} `{!threadG} (args : EntriesToOwnedSliceBlockArgs) (returnAddress : Z) (K : iProp Sigma)  :
  instr_pre 0x800d663c (ZesuSsz.Generated.EntriesToOwnedSlice.FP301.Pilot00e8Entries.fp_machineAt00e8 (args) (returnAddress) (K))%I -∗
  instr_pre 0x800d667c (ZesuSsz.Generated.EntriesToOwnedSlice.FP301.Pilot0128Entries.fp_machineAt0128 (args) (returnAddress) (K))%I -∗
  entriesToOwnedSliceSelectedCode -∗
  instr_body 0x800d6638
    (DesignedEntry_800d6638 args returnAddress K).
Proof.
  zesu_block2.
Qed.

Print Assumptions DesignedBoundary_800d6638.
