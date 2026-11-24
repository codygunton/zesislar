Require Import ZesuSsz.Generated.EntriesToOwnedSlice.FP301.Pilot0204Entries.
Require Import ZesuSsz.Generated.EntriesToOwnedSlice.FP301.Pilot0204Structural.
Require Import ZesuSsz.Generated.EntriesToOwnedSlice.FP301.Pilot021cEntries.
Require Import ZesuSsz.Generated.EntriesToOwnedSlice.FP301.Pilot021cStructural.
Require Import ZesuSsz.Contracts.ZiskMemcpyPremise.
Require Import ZesuSsz.Automation2.All.
Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith NArith.NArith.
Require Import stdpp.bitvector.definitions.
Require Import ZesuSsz.Contracts.EntriesToOwnedSliceBlockEntries.
Require Import ZesuSsz.Contracts.EntriesToOwnedSliceSelected.
Require Import ZesuSsz.Automation2.All.
Local Open Scope Z_scope.
#[local] Typeclasses Transparent entriesToOwnedSliceSelectedCode.

Definition DesignedEntry_800d6758
    `{!islaG Sigma} `{!threadG} (args : EntriesToOwnedSliceBlockArgs) (returnAddress : Z) (K : iProp Sigma) : iProp Sigma :=
  ((ZesuSsz.Generated.EntriesToOwnedSlice.FP301.Pilot0204Entries.fp_machineAt0204 (args) (returnAddress) (K)) ∗
   True)%I.
Global Instance : LithiumUnfold (@DesignedEntry_800d6758) := I.
Global Typeclasses Opaque DesignedEntry_800d6758.

Lemma DesignedBoundary_800d6758 `{!islaG Sigma} `{!threadG} (args : EntriesToOwnedSliceBlockArgs) (returnAddress : Z) (K : iProp Sigma)  :
  instr_pre 0x800d6770 (ZesuSsz.Generated.EntriesToOwnedSlice.FP301.Pilot021cEntries.fp_machineAt021c (args) (returnAddress) (K))%I -∗
  instr_pre 0x800e06c0 (ZesuSsz.Contracts.ZiskMemcpyPremise.ziskMemcpyCallSpec)%I -∗
  entriesToOwnedSliceSelectedCode -∗
  instr_body 0x800d6758
    (DesignedEntry_800d6758 args returnAddress K).
Proof.
  zesu_block2.
Qed.

Print Assumptions DesignedBoundary_800d6758.
