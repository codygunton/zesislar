Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot5e18Entries.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot5e18Structural.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot5d40Entries.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot5d40Structural.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot5e20Entries.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot5e20Structural.
Require Import ZesuSsz.Automation2.All.
Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith NArith.NArith.
Require Import stdpp.bitvector.definitions.
Require Import ZesuSsz.Contracts.ParentHeaderContract.
Require Import ZesuSsz.Contracts.ParentHeaderContract.
Require Import ZesuSsz.Automation2.All.
Local Open Scope Z_scope.
#[local] Typeclasses Transparent parentHeaderSelectedCode.

Definition DesignedEntry_800d5e18
    `{!islaG Sigma} `{!threadG} (args : ParentHeaderArgs) (returnAddress : Z) (K : iProp Sigma) : iProp Sigma :=
  ((ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot5e18Entries.fp_machineAt5e18 (args) (returnAddress) (K)) ∗
   True)%I.
Global Instance : LithiumUnfold (@DesignedEntry_800d5e18) := I.
Global Typeclasses Opaque DesignedEntry_800d5e18.

Lemma DesignedBoundary_800d5e18 `{!islaG Sigma} `{!threadG} (args : ParentHeaderArgs) (returnAddress : Z) (K : iProp Sigma)  :
  instr_pre 0x800d5d40 (ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot5d40Entries.fp_machineAt5d40 (args) (returnAddress) (K))%I -∗
  instr_pre 0x800d5e20 (ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot5e20Entries.fp_machineAt5e20 (args) (returnAddress) (K))%I -∗
  parentHeaderSelectedCode -∗
  instr_body 0x800d5e18
    (DesignedEntry_800d5e18 args returnAddress K).
Proof.
  zesu_block2.
Qed.

Print Assumptions DesignedBoundary_800d5e18.
