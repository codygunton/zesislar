Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot60b8Entries.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot60b8Structural.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot60c0Entries.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot60c0Structural.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot60ccEntries.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot60ccStructural.
Require Import ZesuSsz.Automation2.All.
Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith NArith.NArith.
Require Import stdpp.bitvector.definitions.
Require Import ZesuSsz.Contracts.ParentHeaderContract.
Require Import ZesuSsz.Contracts.ParentHeaderContract.
Require Import ZesuSsz.Automation2.All.
Local Open Scope Z_scope.
#[local] Typeclasses Transparent parentHeaderSelectedCode.

Definition DesignedEntry_800d60b8
    `{!islaG Sigma} `{!threadG} (args : ParentHeaderArgs) (returnAddress : Z) (K : iProp Sigma) : iProp Sigma :=
  ((ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot60b8Entries.fp_machineAt60b8 (args) (returnAddress) (K)) ∗
   True)%I.
Global Instance : LithiumUnfold (@DesignedEntry_800d60b8) := I.
Global Typeclasses Opaque DesignedEntry_800d60b8.

Lemma DesignedBoundary_800d60b8 `{!islaG Sigma} `{!threadG} (args : ParentHeaderArgs) (returnAddress : Z) (K : iProp Sigma)  :
  instr_pre 0x800d60c0 (ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot60c0Entries.fp_machineAt60c0 (args) (returnAddress) (K))%I -∗
  instr_pre 0x800d60cc (ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot60ccEntries.fp_machineAt60cc (args) (returnAddress) (K))%I -∗
  parentHeaderSelectedCode -∗
  instr_body 0x800d60b8
    (DesignedEntry_800d60b8 args returnAddress K).
Proof.
  zesu_block2.
Qed.

Print Assumptions DesignedBoundary_800d60b8.
