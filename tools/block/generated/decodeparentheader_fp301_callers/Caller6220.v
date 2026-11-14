Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot6220Entries.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot6220Structural.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot5f28Entries.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot5f28Structural.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot6228Entries.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot6228Structural.
Require Import ZesuSsz.Automation2.All.
Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith NArith.NArith.
Require Import stdpp.bitvector.definitions.
Require Import ZesuSsz.Contracts.ParentHeaderContract.
Require Import ZesuSsz.Contracts.ParentHeaderContract.
Require Import ZesuSsz.Automation2.All.
Local Open Scope Z_scope.
#[local] Typeclasses Transparent parentHeaderSelectedCode.

Definition DesignedEntry_800d6220
    `{!islaG Sigma} `{!threadG} (args : ParentHeaderArgs) (returnAddress : Z) (K : iProp Sigma) : iProp Sigma :=
  ((ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot6220Entries.fp_machineAt6220 (args) (returnAddress) (K)) ∗
   True)%I.
Global Instance : LithiumUnfold (@DesignedEntry_800d6220) := I.
Global Typeclasses Opaque DesignedEntry_800d6220.

Lemma DesignedBoundary_800d6220 `{!islaG Sigma} `{!threadG} (args : ParentHeaderArgs) (returnAddress : Z) (K : iProp Sigma)  :
  instr_pre 0x800d5f28 (ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot5f28Entries.fp_machineAt5f28 (args) (returnAddress) (K))%I -∗
  instr_pre 0x800d6228 (ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot6228Entries.fp_machineAt6228 (args) (returnAddress) (K))%I -∗
  parentHeaderSelectedCode -∗
  instr_body 0x800d6220
    (DesignedEntry_800d6220 args returnAddress K).
Proof.
  zesu_block2.
Qed.

Print Assumptions DesignedBoundary_800d6220.
