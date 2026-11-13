Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot5d18Entries.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot5d18Structural.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot5d20Entries.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot5d20Structural.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot5d60Entries.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot5d60Structural.
Require Import ZesuSsz.Automation2.All.
Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith NArith.NArith.
Require Import stdpp.bitvector.definitions.
Require Import ZesuSsz.Contracts.ParentHeaderContract.
Require Import ZesuSsz.Contracts.ParentHeaderContract.
Require Import ZesuSsz.Automation2.All.
Local Open Scope Z_scope.
#[local] Typeclasses Transparent parentHeaderSelectedCode.

Definition DesignedEntry_800d5d18
    `{!islaG Sigma} `{!threadG} (args : ParentHeaderArgs) (returnAddress : Z) (K : iProp Sigma) : iProp Sigma :=
  ((ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot5d18Entries.fp_machineAt5d18 (args) (returnAddress) (K)) ∗
   True)%I.
Global Instance : LithiumUnfold (@DesignedEntry_800d5d18) := I.
Global Typeclasses Opaque DesignedEntry_800d5d18.

Lemma DesignedBoundary_800d5d18 `{!islaG Sigma} `{!threadG} (args : ParentHeaderArgs) (returnAddress : Z) (K : iProp Sigma)  :
  instr_pre 0x800d5d20 (ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot5d20Entries.fp_machineAt5d20 (args) (returnAddress) (K))%I -∗
  instr_pre 0x800d5d60 (ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot5d60Entries.fp_machineAt5d60 (args) (returnAddress) (K))%I -∗
  parentHeaderSelectedCode -∗
  instr_body 0x800d5d18
    (DesignedEntry_800d5d18 args returnAddress K).
Proof.
  zesu_block2.
Qed.

Print Assumptions DesignedBoundary_800d5d18.
