Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot5d0cEntries.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot5d0cStructural.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot5d18Entries.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot5d18Structural.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot5d4cEntries.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot5d4cStructural.
Require Import ZesuSsz.Automation2.All.
Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith NArith.NArith.
Require Import stdpp.bitvector.definitions.
Require Import ZesuSsz.Contracts.ParentHeaderContract.
Require Import ZesuSsz.Contracts.ParentHeaderContract.
Require Import ZesuSsz.Automation2.All.
Local Open Scope Z_scope.
#[local] Typeclasses Transparent parentHeaderSelectedCode.

Definition DesignedEntry_800d5d0c
    `{!islaG Sigma} `{!threadG} (args : ParentHeaderArgs) (returnAddress : Z) (K : iProp Sigma) : iProp Sigma :=
  ((ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot5d0cEntries.fp_machineAt5d0c (args) (returnAddress) (K)) ∗
   True)%I.
Global Instance : LithiumUnfold (@DesignedEntry_800d5d0c) := I.
Global Typeclasses Opaque DesignedEntry_800d5d0c.

Lemma DesignedBoundary_800d5d0c `{!islaG Sigma} `{!threadG} (args : ParentHeaderArgs) (returnAddress : Z) (K : iProp Sigma)  :
  instr_pre 0x800d5d18 (ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot5d18Entries.fp_machineAt5d18 (args) (returnAddress) (K))%I -∗
  instr_pre 0x800d5d4c (ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot5d4cEntries.fp_machineAt5d4c (args) (returnAddress) (K))%I -∗
  parentHeaderSelectedCode -∗
  instr_body 0x800d5d0c
    (DesignedEntry_800d5d0c args returnAddress K).
Proof.
  zesu_block2.
Qed.

Print Assumptions DesignedBoundary_800d5d0c.
