Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot059cEntries.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot059cStructural.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot0270Entries.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot0270Structural.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot05a4Entries.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot05a4Structural.
Require Import ZesuSsz.Automation2.All.
Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith NArith.NArith.
Require Import stdpp.bitvector.definitions.
Require Import ZesuSsz.Contracts.ParentHeaderContract.
Require Import ZesuSsz.Contracts.ParentHeaderContract.
Require Import ZesuSsz.Automation2.All.
Local Open Scope Z_scope.
#[local] Typeclasses Transparent parentHeaderSelectedCode.

Definition DesignedEntry_800d6254
    `{!islaG Sigma} `{!threadG} (args : ParentHeaderArgs) (returnAddress : Z) (K : iProp Sigma) : iProp Sigma :=
  ((ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot059cEntries.fp_machineAt059c (args) (returnAddress) (K)) ∗
   True)%I.
Global Instance : LithiumUnfold (@DesignedEntry_800d6254) := I.
Global Typeclasses Opaque DesignedEntry_800d6254.

Lemma DesignedBoundary_800d6254 `{!islaG Sigma} `{!threadG} (args : ParentHeaderArgs) (returnAddress : Z) (K : iProp Sigma)  :
  instr_pre 0x800d5f28 (ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot0270Entries.fp_machineAt0270 (args) (returnAddress) (K))%I -∗
  instr_pre 0x800d625c (ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot05a4Entries.fp_machineAt05a4 (args) (returnAddress) (K))%I -∗
  parentHeaderSelectedCode -∗
  instr_body 0x800d6254
    (DesignedEntry_800d6254 args returnAddress K).
Proof.
  zesu_block2.
Qed.

Print Assumptions DesignedBoundary_800d6254.
