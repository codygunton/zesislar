Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot0054Entries.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot0054Structural.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot0060Entries.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot0060Structural.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot0094Entries.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot0094Structural.
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
  ((ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot0054Entries.fp_machineAt0054 (args) (returnAddress) (K)) ∗
   True)%I.
Global Instance : LithiumUnfold (@DesignedEntry_800d5d0c) := I.
Global Typeclasses Opaque DesignedEntry_800d5d0c.

Lemma DesignedBoundary_800d5d0c `{!islaG Sigma} `{!threadG} (args : ParentHeaderArgs) (returnAddress : Z) (K : iProp Sigma)  :
  instr_pre 0x800d5d18 (ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot0060Entries.fp_machineAt0060 (args) (returnAddress) (K))%I -∗
  instr_pre 0x800d5d4c (ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot0094Entries.fp_machineAt0094 (args) (returnAddress) (K))%I -∗
  parentHeaderSelectedCode -∗
  instr_body 0x800d5d0c
    (DesignedEntry_800d5d0c args returnAddress K).
Proof.
  zesu_block2.
Qed.

Print Assumptions DesignedBoundary_800d5d0c.
