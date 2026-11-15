Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot0040Entries.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot0040Structural.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot0048Entries.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot0048Structural.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot0054Entries.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot0054Structural.
Require Import ZesuSsz.Automation2.All.
Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith NArith.NArith.
Require Import stdpp.bitvector.definitions.
Require Import ZesuSsz.Contracts.ParentHeaderContract.
Require Import ZesuSsz.Contracts.ParentHeaderContract.
Require Import ZesuSsz.Automation2.All.
Local Open Scope Z_scope.
#[local] Typeclasses Transparent parentHeaderSelectedCode.

Definition DesignedEntry_800d5cf8
    `{!islaG Sigma} `{!threadG} (args : ParentHeaderArgs) (returnAddress : Z) (K : iProp Sigma) : iProp Sigma :=
  ((ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot0040Entries.fp_machineAt0040 (args) (returnAddress) (K)) ∗
   True)%I.
Global Instance : LithiumUnfold (@DesignedEntry_800d5cf8) := I.
Global Typeclasses Opaque DesignedEntry_800d5cf8.

Lemma DesignedBoundary_800d5cf8 `{!islaG Sigma} `{!threadG} (args : ParentHeaderArgs) (returnAddress : Z) (K : iProp Sigma)  :
  instr_pre 0x800d5d00 (ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot0048Entries.fp_machineAt0048 (args) (returnAddress) (K))%I -∗
  instr_pre 0x800d5d0c (ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot0054Entries.fp_machineAt0054 (args) (returnAddress) (K))%I -∗
  parentHeaderSelectedCode -∗
  instr_body 0x800d5cf8
    (DesignedEntry_800d5cf8 args returnAddress K).
Proof.
  zesu_block2.
Qed.

Print Assumptions DesignedBoundary_800d5cf8.
