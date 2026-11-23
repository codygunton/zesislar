Require Import ZesuSsz.Generated.EntriesToOwnedSlice.FP301.Pilot0144Entries.
Require Import ZesuSsz.Generated.EntriesToOwnedSlice.FP301.Pilot0144Structural.
Require Import ZesuSsz.Generated.EntriesToOwnedSlice.FP301.Pilot014cEntries.
Require Import ZesuSsz.Generated.EntriesToOwnedSlice.FP301.Pilot014cStructural.
Require Import ZesuSsz.Automation2.All.
Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith NArith.NArith.
Require Import stdpp.bitvector.definitions.
Require Import ZesuSsz.Contracts.EntriesToOwnedSliceBlockEntries.
Require Import ZesuSsz.Contracts.EntriesToOwnedSliceSelected.
Require Import ZesuSsz.Generated.EntriesToOwnedSlice.FP301.Edges0144.
Require Import ZesuSsz.Automation2.All.
Local Open Scope Z_scope.
#[local] Typeclasses Transparent entriesToOwnedSliceSelectedCode.

Definition DesignedEntry_800d6698
    `{!islaG Sigma} `{!threadG} (args : EntriesToOwnedSliceBlockArgs) (returnAddress : Z) (K : iProp Sigma) : iProp Sigma :=
  ((ZesuSsz.Generated.EntriesToOwnedSlice.FP301.Pilot0144Entries.fp_machineAt0144 (args) (returnAddress) (K)) ∗
   True)%I.
Global Instance : LithiumUnfold (@DesignedEntry_800d6698) := I.
Global Typeclasses Opaque DesignedEntry_800d6698.

Lemma DesignedBoundary_800d6698 `{!islaG Sigma} `{!threadG} (args : EntriesToOwnedSliceBlockArgs) (returnAddress : Z) (K : iProp Sigma)  :
  instr_pre 0x800d66a0 (ZesuSsz.Generated.EntriesToOwnedSlice.FP301.Pilot014cEntries.fp_machineAt014c_slot0 (args) (returnAddress) (K))%I -∗
  entriesToOwnedSliceSelectedCode -∗
  instr_body 0x800d6698
    (DesignedEntry_800d6698 args returnAddress K).
Proof.
  zesu_block2.
Qed.

Print Assumptions DesignedBoundary_800d6698.
