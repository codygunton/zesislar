Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot5ef4Entries.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot5ef4Structural.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot5d40Entries.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot5d40Structural.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot5efcEntries.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot5efcStructural.
Require Import ZesuSsz.Automation2.All.
Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith NArith.NArith.
Require Import stdpp.bitvector.definitions.
Require Import ZesuSsz.Contracts.ParentHeaderContract.
Require Import ZesuSsz.Contracts.ParentHeaderContract.
Require Import ZesuSsz.Automation2.All.
Local Open Scope Z_scope.
#[local] Typeclasses Transparent parentHeaderSelectedCode.

Definition DesignedEntry_800d5ef4
    `{!islaG Sigma} `{!threadG} (args : ParentHeaderArgs) (returnAddress : Z) (K : iProp Sigma) : iProp Sigma :=
  ((ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot5ef4Entries.fp_machineAt5ef4 (args) (returnAddress) (K)) ∗
   True)%I.
Global Instance : LithiumUnfold (@DesignedEntry_800d5ef4) := I.
Global Typeclasses Opaque DesignedEntry_800d5ef4.

Lemma DesignedBoundary_800d5ef4 `{!islaG Sigma} `{!threadG} (args : ParentHeaderArgs) (returnAddress : Z) (K : iProp Sigma)  :
  instr_pre 0x800d5d40 (ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot5d40Entries.fp_machineAt5d40 (args) (returnAddress) (K))%I -∗
  instr_pre 0x800d5efc (ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot5efcEntries.fp_machineAt5efc (args) (returnAddress) (K))%I -∗
  parentHeaderSelectedCode -∗
  instr_body 0x800d5ef4
    (DesignedEntry_800d5ef4 args returnAddress K).
Proof.
  zesu_block2.
Qed.

Print Assumptions DesignedBoundary_800d5ef4.
