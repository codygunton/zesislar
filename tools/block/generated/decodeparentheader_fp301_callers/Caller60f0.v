Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot60f0Entries.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot60f0Structural.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot60c0Entries.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot60c0Structural.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot60f8Entries.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot60f8Structural.
Require Import ZesuSsz.Automation2.All.
Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith NArith.NArith.
Require Import stdpp.bitvector.definitions.
Require Import ZesuSsz.Contracts.ParentHeaderContract.
Require Import ZesuSsz.Contracts.ParentHeaderContract.
Require Import ZesuSsz.Automation2.All.
Local Open Scope Z_scope.
#[local] Typeclasses Transparent parentHeaderSelectedCode.

Definition DesignedEntry_800d60f0
    `{!islaG Sigma} `{!threadG} (args : ParentHeaderArgs) (returnAddress : Z) (K : iProp Sigma) : iProp Sigma :=
  ((ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot60f0Entries.fp_machineAt60f0 (args) (returnAddress) (K)) ∗
   True)%I.
Global Instance : LithiumUnfold (@DesignedEntry_800d60f0) := I.
Global Typeclasses Opaque DesignedEntry_800d60f0.

Lemma DesignedBoundary_800d60f0 `{!islaG Sigma} `{!threadG} (args : ParentHeaderArgs) (returnAddress : Z) (K : iProp Sigma)  :
  instr_pre 0x800d60c0 (ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot60c0Entries.fp_machineAt60c0 (args) (returnAddress) (K))%I -∗
  instr_pre 0x800d60f8 (ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot60f8Entries.fp_machineAt60f8 (args) (returnAddress) (K))%I -∗
  parentHeaderSelectedCode -∗
  instr_body 0x800d60f0
    (DesignedEntry_800d60f0 args returnAddress K).
Proof.
  zesu_block2.
Qed.

Print Assumptions DesignedBoundary_800d60f0.
