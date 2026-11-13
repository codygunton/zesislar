Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot5e4cEntries.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot5e4cStructural.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot5d60Entries.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot5d60Structural.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot5e54Entries.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot5e54Structural.
Require Import ZesuSsz.Automation2.All.
Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith NArith.NArith.
Require Import stdpp.bitvector.definitions.
Require Import ZesuSsz.Contracts.ParentHeaderContract.
Require Import ZesuSsz.Contracts.ParentHeaderContract.
Require Import ZesuSsz.Automation2.All.
Local Open Scope Z_scope.
#[local] Typeclasses Transparent parentHeaderSelectedCode.

Definition DesignedEntry_800d5e4c
    `{!islaG Sigma} `{!threadG} (args : ParentHeaderArgs) (returnAddress : Z) (K : iProp Sigma) : iProp Sigma :=
  ((ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot5e4cEntries.fp_machineAt5e4c (args) (returnAddress) (K)) ∗
   True)%I.
Global Instance : LithiumUnfold (@DesignedEntry_800d5e4c) := I.
Global Typeclasses Opaque DesignedEntry_800d5e4c.

Lemma DesignedBoundary_800d5e4c `{!islaG Sigma} `{!threadG} (args : ParentHeaderArgs) (returnAddress : Z) (K : iProp Sigma)  :
  instr_pre 0x800d5d60 (ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot5d60Entries.fp_machineAt5d60 (args) (returnAddress) (K))%I -∗
  instr_pre 0x800d5e54 (ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot5e54Entries.fp_machineAt5e54 (args) (returnAddress) (K))%I -∗
  parentHeaderSelectedCode -∗
  instr_body 0x800d5e4c
    (DesignedEntry_800d5e4c args returnAddress K).
Proof.
  zesu_block2.
Qed.

Print Assumptions DesignedBoundary_800d5e4c.
