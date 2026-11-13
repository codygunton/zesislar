Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot5f5cEntries.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot5f5cStructural.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot5f24Entries.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot5f24Structural.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot5f68Entries.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot5f68Structural.
Require Import ZesuSsz.Automation2.All.
Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith NArith.NArith.
Require Import stdpp.bitvector.definitions.
Require Import ZesuSsz.Contracts.ParentHeaderContract.
Require Import ZesuSsz.Contracts.ParentHeaderContract.
Require Import ZesuSsz.Automation2.All.
Local Open Scope Z_scope.
#[local] Typeclasses Transparent parentHeaderSelectedCode.

Definition DesignedEntry_800d5f5c
    `{!islaG Sigma} `{!threadG} (args : ParentHeaderArgs) (returnAddress : Z) (K : iProp Sigma) : iProp Sigma :=
  ((ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot5f5cEntries.fp_machineAt5f5c (args) (returnAddress) (K)) ∗
   True)%I.
Global Instance : LithiumUnfold (@DesignedEntry_800d5f5c) := I.
Global Typeclasses Opaque DesignedEntry_800d5f5c.

Lemma DesignedBoundary_800d5f5c `{!islaG Sigma} `{!threadG} (args : ParentHeaderArgs) (returnAddress : Z) (K : iProp Sigma)  :
  instr_pre 0x800d5f24 (ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot5f24Entries.fp_machineAt5f24 (args) (returnAddress) (K))%I -∗
  instr_pre 0x800d5f68 (ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot5f68Entries.fp_machineAt5f68 (args) (returnAddress) (K))%I -∗
  parentHeaderSelectedCode -∗
  instr_body 0x800d5f5c
    (DesignedEntry_800d5f5c args returnAddress K).
Proof.
  zesu_block2.
Qed.

Print Assumptions DesignedBoundary_800d5f5c.
