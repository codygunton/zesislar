Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot0094Entries.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot0094Structural.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot00b0Entries.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot00b0Structural.
Require Import ZesuSsz.Automation2.All.
Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith NArith.NArith.
Require Import stdpp.bitvector.definitions.
Require Import ZesuSsz.Contracts.ParentHeaderContract.
Require Import ZesuSsz.Contracts.ParentHeaderContract.
Require Import ZesuSsz.Automation2.All.
Local Open Scope Z_scope.
#[local] Typeclasses Transparent parentHeaderSelectedCode.

Definition DesignedEntry_800d5d4c
    `{!islaG Sigma} `{!threadG} (args : ParentHeaderArgs) (returnAddress : Z) (K : iProp Sigma) : iProp Sigma :=
  ((ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot0094Entries.fp_machineAt0094 (args) (returnAddress) (K)) ∗
   True)%I.
Global Instance : LithiumUnfold (@DesignedEntry_800d5d4c) := I.
Global Typeclasses Opaque DesignedEntry_800d5d4c.

Lemma DesignedBoundary_800d5d4c `{!islaG Sigma} `{!threadG} (args : ParentHeaderArgs) (returnAddress : Z) (K : iProp Sigma)  :
  instr_pre 0x800d5d68 (ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot00b0Entries.fp_machineAt00b0 (args) (returnAddress) (K))%I -∗
  parentHeaderSelectedCode -∗
  instr_body 0x800d5d4c
    (DesignedEntry_800d5d4c args returnAddress K).
Proof.
  zesu_block2.
Qed.

Print Assumptions DesignedBoundary_800d5d4c.
