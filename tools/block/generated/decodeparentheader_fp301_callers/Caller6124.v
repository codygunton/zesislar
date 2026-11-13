Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot6124Entries.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot6124Structural.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot6144Entries.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot6144Structural.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot6150Entries.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot6150Structural.
Require Import ZesuSsz.Automation2.All.
Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith NArith.NArith.
Require Import stdpp.bitvector.definitions.
Require Import ZesuSsz.Contracts.ParentHeaderContract.
Require Import ZesuSsz.Contracts.ParentHeaderContract.
Require Import ZesuSsz.Automation2.All.
Local Open Scope Z_scope.
#[local] Typeclasses Transparent parentHeaderSelectedCode.

Definition DesignedEntry_800d6124
    `{!islaG Sigma} `{!threadG} (args : ParentHeaderArgs) (returnAddress : Z) (K : iProp Sigma) : iProp Sigma :=
  ((ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot6124Entries.fp_machineAt6124 (args) (returnAddress) (K)) ∗
   True)%I.
Global Instance : LithiumUnfold (@DesignedEntry_800d6124) := I.
Global Typeclasses Opaque DesignedEntry_800d6124.

Lemma DesignedBoundary_800d6124 `{!islaG Sigma} `{!threadG} (args : ParentHeaderArgs) (returnAddress : Z) (K : iProp Sigma)  :
  instr_pre 0x800d6144 (ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot6144Entries.fp_machineAt6144 (args) (returnAddress) (K))%I -∗
  instr_pre 0x800d6150 (ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot6150Entries.fp_machineAt6150 (args) (returnAddress) (K))%I -∗
  parentHeaderSelectedCode -∗
  instr_body 0x800d6124
    (DesignedEntry_800d6124 args returnAddress K).
Proof.
  zesu_block2.
Qed.

Print Assumptions DesignedBoundary_800d6124.
