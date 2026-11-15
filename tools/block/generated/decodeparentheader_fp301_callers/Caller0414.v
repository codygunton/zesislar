Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot0414Entries.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot0414Structural.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot03bcEntries.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot03bcStructural.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot041cEntries.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot041cStructural.
Require Import ZesuSsz.Automation2.All.
Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith NArith.NArith.
Require Import stdpp.bitvector.definitions.
Require Import ZesuSsz.Contracts.ParentHeaderContract.
Require Import ZesuSsz.Contracts.ParentHeaderContract.
Require Import ZesuSsz.Automation2.All.
Local Open Scope Z_scope.
#[local] Typeclasses Transparent parentHeaderSelectedCode.

Definition DesignedEntry_800d60cc
    `{!islaG Sigma} `{!threadG} (args : ParentHeaderArgs) (returnAddress : Z) (K : iProp Sigma) : iProp Sigma :=
  ((ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot0414Entries.fp_machineAt0414 (args) (returnAddress) (K)) ∗
   True)%I.
Global Instance : LithiumUnfold (@DesignedEntry_800d60cc) := I.
Global Typeclasses Opaque DesignedEntry_800d60cc.

Lemma DesignedBoundary_800d60cc `{!islaG Sigma} `{!threadG} (args : ParentHeaderArgs) (returnAddress : Z) (K : iProp Sigma)  :
  instr_pre 0x800d6074 (ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot03bcEntries.fp_machineAt03bc (args) (returnAddress) (K))%I -∗
  instr_pre 0x800d60d4 (ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot041cEntries.fp_machineAt041c (args) (returnAddress) (K))%I -∗
  parentHeaderSelectedCode -∗
  instr_body 0x800d60cc
    (DesignedEntry_800d60cc args returnAddress K).
Proof.
  zesu_block2.
Qed.

Print Assumptions DesignedBoundary_800d60cc.
