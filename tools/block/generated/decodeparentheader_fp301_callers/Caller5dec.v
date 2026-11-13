Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot5decEntries.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot5decStructural.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot5d40Entries.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot5d40Structural.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot5df4Entries.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot5df4Structural.
Require Import ZesuSsz.Automation2.All.
Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith NArith.NArith.
Require Import stdpp.bitvector.definitions.
Require Import ZesuSsz.Contracts.ParentHeaderContract.
Require Import ZesuSsz.Contracts.ParentHeaderContract.
Require Import ZesuSsz.Automation2.All.
Local Open Scope Z_scope.
#[local] Typeclasses Transparent parentHeaderSelectedCode.

Definition DesignedEntry_800d5dec
    `{!islaG Sigma} `{!threadG} (args : ParentHeaderArgs) (returnAddress : Z) (K : iProp Sigma) : iProp Sigma :=
  ((ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot5decEntries.fp_machineAt5dec (args) (returnAddress) (K)) ∗
   True)%I.
Global Instance : LithiumUnfold (@DesignedEntry_800d5dec) := I.
Global Typeclasses Opaque DesignedEntry_800d5dec.

Lemma DesignedBoundary_800d5dec `{!islaG Sigma} `{!threadG} (args : ParentHeaderArgs) (returnAddress : Z) (K : iProp Sigma)  :
  instr_pre 0x800d5d40 (ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot5d40Entries.fp_machineAt5d40 (args) (returnAddress) (K))%I -∗
  instr_pre 0x800d5df4 (ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot5df4Entries.fp_machineAt5df4 (args) (returnAddress) (K))%I -∗
  parentHeaderSelectedCode -∗
  instr_body 0x800d5dec
    (DesignedEntry_800d5dec args returnAddress K).
Proof.
  zesu_block2.
Qed.

Print Assumptions DesignedBoundary_800d5dec.
