Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot6034Entries.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot6034Structural.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot5f24Entries.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot5f24Structural.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot6040Entries.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot6040Structural.
Require Import ZesuSsz.Automation2.All.
Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith NArith.NArith.
Require Import stdpp.bitvector.definitions.
Require Import ZesuSsz.Contracts.ParentHeaderContract.
Require Import ZesuSsz.Contracts.ParentHeaderContract.
Require Import ZesuSsz.Automation2.All.
Local Open Scope Z_scope.
#[local] Typeclasses Transparent parentHeaderSelectedCode.

Definition DesignedEntry_800d6034
    `{!islaG Sigma} `{!threadG} (args : ParentHeaderArgs) (returnAddress : Z) (K : iProp Sigma) : iProp Sigma :=
  ((ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot6034Entries.fp_machineAt6034 (args) (returnAddress) (K)) ∗
   True)%I.
Global Instance : LithiumUnfold (@DesignedEntry_800d6034) := I.
Global Typeclasses Opaque DesignedEntry_800d6034.

Lemma DesignedBoundary_800d6034 `{!islaG Sigma} `{!threadG} (args : ParentHeaderArgs) (returnAddress : Z) (K : iProp Sigma)  :
  instr_pre 0x800d5f24 (ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot5f24Entries.fp_machineAt5f24 (args) (returnAddress) (K))%I -∗
  instr_pre 0x800d6040 (ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot6040Entries.fp_machineAt6040 (args) (returnAddress) (K))%I -∗
  parentHeaderSelectedCode -∗
  instr_body 0x800d6034
    (DesignedEntry_800d6034 args returnAddress K).
Proof.
  zesu_block2.
Qed.

Print Assumptions DesignedBoundary_800d6034.
