Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot5dc0Entries.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot5dc0Structural.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot5d40Entries.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot5d40Structural.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot5dc8Entries.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot5dc8Structural.
Require Import ZesuSsz.Automation2.All.
Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith NArith.NArith.
Require Import stdpp.bitvector.definitions.
Require Import ZesuSsz.Contracts.ParentHeaderContract.
Require Import ZesuSsz.Contracts.ParentHeaderContract.
Require Import ZesuSsz.Automation2.All.
Local Open Scope Z_scope.
#[local] Typeclasses Transparent parentHeaderSelectedCode.

Definition DesignedEntry_800d5dc0
    `{!islaG Sigma} `{!threadG} (args : ParentHeaderArgs) (returnAddress : Z) (K : iProp Sigma) : iProp Sigma :=
  ((ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot5dc0Entries.fp_machineAt5dc0 (args) (returnAddress) (K)) ∗
   True)%I.
Global Instance : LithiumUnfold (@DesignedEntry_800d5dc0) := I.
Global Typeclasses Opaque DesignedEntry_800d5dc0.

Lemma DesignedBoundary_800d5dc0 `{!islaG Sigma} `{!threadG} (args : ParentHeaderArgs) (returnAddress : Z) (K : iProp Sigma)  :
  instr_pre 0x800d5d40 (ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot5d40Entries.fp_machineAt5d40 (args) (returnAddress) (K))%I -∗
  instr_pre 0x800d5dc8 (ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot5dc8Entries.fp_machineAt5dc8 (args) (returnAddress) (K))%I -∗
  parentHeaderSelectedCode -∗
  instr_body 0x800d5dc0
    (DesignedEntry_800d5dc0 args returnAddress K).
Proof.
  zesu_block2.
Qed.

Print Assumptions DesignedBoundary_800d5dc0.
