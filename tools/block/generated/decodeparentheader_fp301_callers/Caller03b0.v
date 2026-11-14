Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot03b0Entries.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot03b0Structural.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot03bcEntries.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot03bcStructural.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot03e8Entries.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot03e8Structural.
Require Import ZesuSsz.Automation2.All.
Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith NArith.NArith.
Require Import stdpp.bitvector.definitions.
Require Import ZesuSsz.Contracts.ParentHeaderContract.
Require Import ZesuSsz.Contracts.ParentHeaderContract.
Require Import ZesuSsz.Automation2.All.
Local Open Scope Z_scope.
#[local] Typeclasses Transparent parentHeaderSelectedCode.

Definition DesignedEntry_800d6068
    `{!islaG Sigma} `{!threadG} (args : ParentHeaderArgs) (returnAddress : Z) (K : iProp Sigma) : iProp Sigma :=
  ((ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot03b0Entries.fp_machineAt03b0 (args) (returnAddress) (K)) ∗
   True)%I.
Global Instance : LithiumUnfold (@DesignedEntry_800d6068) := I.
Global Typeclasses Opaque DesignedEntry_800d6068.

Lemma DesignedBoundary_800d6068 `{!islaG Sigma} `{!threadG} (args : ParentHeaderArgs) (returnAddress : Z) (K : iProp Sigma)  :
  instr_pre 0x800d6074 (ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot03bcEntries.fp_machineAt03bc (args) (returnAddress) (K))%I -∗
  instr_pre 0x800d60a0 (ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot03e8Entries.fp_machineAt03e8 (args) (returnAddress) (K))%I -∗
  parentHeaderSelectedCode -∗
  instr_body 0x800d6068
    (DesignedEntry_800d6068 args returnAddress K).
Proof.
  zesu_block2.
Qed.

Print Assumptions DesignedBoundary_800d6068.
