Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot6254Entries.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot6254Structural.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot5f28Entries.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot5f28Structural.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot625cEntries.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot625cStructural.
Require Import ZesuSsz.Automation2.All.
Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith NArith.NArith.
Require Import stdpp.bitvector.definitions.
Require Import ZesuSsz.Contracts.ParentHeaderContract.
Require Import ZesuSsz.Contracts.ParentHeaderContract.
Require Import ZesuSsz.Automation2.All.
Local Open Scope Z_scope.
#[local] Typeclasses Transparent parentHeaderSelectedCode.

Definition DesignedEntry_800d6254
    `{!islaG Sigma} `{!threadG} (args : ParentHeaderArgs) (returnAddress : Z) (K : iProp Sigma) : iProp Sigma :=
  ((ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot6254Entries.fp_machineAt6254 (args) (returnAddress) (K)) ∗
   True)%I.
Global Instance : LithiumUnfold (@DesignedEntry_800d6254) := I.
Global Typeclasses Opaque DesignedEntry_800d6254.

Lemma DesignedBoundary_800d6254 `{!islaG Sigma} `{!threadG} (args : ParentHeaderArgs) (returnAddress : Z) (K : iProp Sigma)  :
  instr_pre 0x800d5f28 (ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot5f28Entries.fp_machineAt5f28 (args) (returnAddress) (K))%I -∗
  instr_pre 0x800d625c (ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot625cEntries.fp_machineAt625c (args) (returnAddress) (K))%I -∗
  parentHeaderSelectedCode -∗
  instr_body 0x800d6254
    (DesignedEntry_800d6254 args returnAddress K).
Proof.
  zesu_block2.
Qed.

Print Assumptions DesignedBoundary_800d6254.
