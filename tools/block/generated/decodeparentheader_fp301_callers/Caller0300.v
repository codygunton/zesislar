Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot0300Entries.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot0300Structural.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot026cEntries.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot026cStructural.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot0308Entries.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot0308Structural.
Require Import ZesuSsz.Automation2.All.
Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith NArith.NArith.
Require Import stdpp.bitvector.definitions.
Require Import ZesuSsz.Contracts.ParentHeaderContract.
Require Import ZesuSsz.Contracts.ParentHeaderContract.
Require Import ZesuSsz.Automation2.All.
Local Open Scope Z_scope.
#[local] Typeclasses Transparent parentHeaderSelectedCode.

Definition DesignedEntry_800d5fb8
    `{!islaG Sigma} `{!threadG} (args : ParentHeaderArgs) (returnAddress : Z) (K : iProp Sigma) : iProp Sigma :=
  ((ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot0300Entries.fp_machineAt0300 (args) (returnAddress) (K)) ∗
   True)%I.
Global Instance : LithiumUnfold (@DesignedEntry_800d5fb8) := I.
Global Typeclasses Opaque DesignedEntry_800d5fb8.

Lemma DesignedBoundary_800d5fb8 `{!islaG Sigma} `{!threadG} (args : ParentHeaderArgs) (returnAddress : Z) (K : iProp Sigma)  :
  instr_pre 0x800d5f24 (ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot026cEntries.fp_machineAt026c (args) (returnAddress) (K))%I -∗
  instr_pre 0x800d5fc0 (ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot0308Entries.fp_machineAt0308 (args) (returnAddress) (K))%I -∗
  parentHeaderSelectedCode -∗
  instr_body 0x800d5fb8
    (DesignedEntry_800d5fb8 args returnAddress K).
Proof.
  zesu_block2.
Qed.

Print Assumptions DesignedBoundary_800d5fb8.
