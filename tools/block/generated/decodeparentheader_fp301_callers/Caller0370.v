Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot0370Entries.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot0370Structural.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot026cEntries.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot026cStructural.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot037cEntries.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot037cStructural.
Require Import ZesuSsz.Automation2.All.
Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith NArith.NArith.
Require Import stdpp.bitvector.definitions.
Require Import ZesuSsz.Contracts.ParentHeaderContract.
Require Import ZesuSsz.Contracts.ParentHeaderContract.
Require Import ZesuSsz.Automation2.All.
Local Open Scope Z_scope.
#[local] Typeclasses Transparent parentHeaderSelectedCode.

Definition DesignedEntry_800d6028
    `{!islaG Sigma} `{!threadG} (args : ParentHeaderArgs) (returnAddress : Z) (K : iProp Sigma) : iProp Sigma :=
  ((ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot0370Entries.fp_machineAt0370 (args) (returnAddress) (K)) ∗
   True)%I.
Global Instance : LithiumUnfold (@DesignedEntry_800d6028) := I.
Global Typeclasses Opaque DesignedEntry_800d6028.

Lemma DesignedBoundary_800d6028 `{!islaG Sigma} `{!threadG} (args : ParentHeaderArgs) (returnAddress : Z) (K : iProp Sigma)  :
  instr_pre 0x800d5f24 (ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot026cEntries.fp_machineAt026c (args) (returnAddress) (K))%I -∗
  instr_pre 0x800d6034 (ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot037cEntries.fp_machineAt037c (args) (returnAddress) (K))%I -∗
  parentHeaderSelectedCode -∗
  instr_body 0x800d6028
    (DesignedEntry_800d6028 args returnAddress K).
Proof.
  zesu_block2.
Qed.

Print Assumptions DesignedBoundary_800d6028.
