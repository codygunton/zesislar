Require Import ZesuSsz.Generated.EntriesToOwnedSlice.FP301.Pilot021cEntries.
Require Import ZesuSsz.Generated.EntriesToOwnedSlice.FP301.Pilot021cStructural.
Require Import ZesuSsz.Generated.EntriesToOwnedSlice.FP301.Pilot01c8Entries.
Require Import ZesuSsz.Generated.EntriesToOwnedSlice.FP301.Pilot01c8Structural.
Require Import ZesuSsz.Generated.EntriesToOwnedSlice.FP301.Pilot0224Entries.
Require Import ZesuSsz.Generated.EntriesToOwnedSlice.FP301.Pilot0224Structural.
Require Import ZesuSsz.Automation2.All.
Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith NArith.NArith.
Require Import stdpp.bitvector.definitions.
Require Import ZesuSsz.Contracts.EntriesToOwnedSliceBlockEntries.
Require Import ZesuSsz.Contracts.EntriesToOwnedSliceSelected.
Require Import ZesuSsz.Automation2.All.
Local Open Scope Z_scope.
#[local] Typeclasses Transparent entriesToOwnedSliceSelectedCode.

Definition DesignedEntry_800d6770
    `{!islaG Sigma} `{!threadG} (args : EntriesToOwnedSliceBlockArgs) (returnAddress : Z) (K : iProp Sigma) : iProp Sigma :=
  ((ZesuSsz.Generated.EntriesToOwnedSlice.FP301.Pilot021cEntries.fp_machineAt021c (args) (returnAddress) (K)) ∗
   True)%I.
Global Instance : LithiumUnfold (@DesignedEntry_800d6770) := I.
Global Typeclasses Opaque DesignedEntry_800d6770.

Lemma DesignedBoundary_800d6770 `{!islaG Sigma} `{!threadG} (args : EntriesToOwnedSliceBlockArgs) (returnAddress : Z) (K : iProp Sigma)  :
  instr_pre 0x800d671c (ZesuSsz.Generated.EntriesToOwnedSlice.FP301.Pilot01c8Entries.fp_machineAt01c8 (args) (returnAddress) (K))%I -∗
  instr_pre 0x800d6778 (ZesuSsz.Generated.EntriesToOwnedSlice.FP301.Pilot0224Entries.fp_machineAt0224 (args) (returnAddress) (K))%I -∗
  entriesToOwnedSliceSelectedCode -∗
  instr_body 0x800d6770
    (DesignedEntry_800d6770 args returnAddress K).
Proof.
  zesu_block2.
Qed.

Print Assumptions DesignedBoundary_800d6770.
