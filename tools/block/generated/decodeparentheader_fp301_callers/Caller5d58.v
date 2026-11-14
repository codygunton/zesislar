Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot5d58Entries.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot5d58Structural.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot5d60Entries.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot5d60Structural.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot5da4Entries.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot5da4Structural.
Require Import ZesuSsz.Automation2.All.
Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith NArith.NArith.
Require Import stdpp.bitvector.definitions.
Require Import ZesuSsz.Contracts.ParentHeaderContract.
Require Import ZesuSsz.Contracts.ParentHeaderContract.
Require Import ZesuSsz.Automation2.All.
Local Open Scope Z_scope.
#[local] Typeclasses Transparent parentHeaderSelectedCode.

Definition DesignedEntry_800d5d58
    `{!islaG Sigma} `{!threadG} (args : ParentHeaderArgs) (returnAddress : Z) (K : iProp Sigma) : iProp Sigma :=
  ((ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot5d58Entries.fp_machineAt5d58 (args) (returnAddress) (K)) ∗
   True)%I.
Global Instance : LithiumUnfold (@DesignedEntry_800d5d58) := I.
Global Typeclasses Opaque DesignedEntry_800d5d58.

Lemma DesignedBoundary_800d5d58 `{!islaG Sigma} `{!threadG} (args : ParentHeaderArgs) (returnAddress : Z) (K : iProp Sigma)  :
  instr_pre 0x800d5d60 (ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot5d60Entries.fp_machineAt5d60 (args) (returnAddress) (K))%I -∗
  instr_pre 0x800d5da4 (ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot5da4Entries.fp_machineAt5da4 (args) (returnAddress) (K))%I -∗
  parentHeaderSelectedCode -∗
  instr_body 0x800d5d58
    (DesignedEntry_800d5d58 args returnAddress K).
Proof.
  zesu_block2.
Qed.

Print Assumptions DesignedBoundary_800d5d58.
