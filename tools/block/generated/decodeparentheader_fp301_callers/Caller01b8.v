Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot01b8Entries.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot01b8Structural.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot0088Entries.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot0088Structural.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot01c0Entries.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot01c0Structural.
Require Import ZesuSsz.Automation2.All.
Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith NArith.NArith.
Require Import stdpp.bitvector.definitions.
Require Import ZesuSsz.Contracts.ParentHeaderContract.
Require Import ZesuSsz.Contracts.ParentHeaderContract.
Require Import ZesuSsz.Automation2.All.
Local Open Scope Z_scope.
#[local] Typeclasses Transparent parentHeaderSelectedCode.

Definition DesignedEntry_800d5e70
    `{!islaG Sigma} `{!threadG} (args : ParentHeaderArgs) (returnAddress : Z) (K : iProp Sigma) : iProp Sigma :=
  ((ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot01b8Entries.fp_machineAt01b8 (args) (returnAddress) (K)) ∗
   True)%I.
Global Instance : LithiumUnfold (@DesignedEntry_800d5e70) := I.
Global Typeclasses Opaque DesignedEntry_800d5e70.

Lemma DesignedBoundary_800d5e70 `{!islaG Sigma} `{!threadG} (args : ParentHeaderArgs) (returnAddress : Z) (K : iProp Sigma)  :
  instr_pre 0x800d5d40 (ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot0088Entries.fp_machineAt0088 (args) (returnAddress) (K))%I -∗
  instr_pre 0x800d5e78 (ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot01c0Entries.fp_machineAt01c0 (args) (returnAddress) (K))%I -∗
  parentHeaderSelectedCode -∗
  instr_body 0x800d5e70
    (DesignedEntry_800d5e70 args returnAddress K).
Proof.
  zesu_block2.
Qed.

Print Assumptions DesignedBoundary_800d5e70.
