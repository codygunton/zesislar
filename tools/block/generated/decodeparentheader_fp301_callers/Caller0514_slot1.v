Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot0514Entries.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot0514Structural.
Require Import ZesuSsz.Compliance.ParentHeaderCompositionBoundary.
Require Import ZesuSsz.Automation2.All.
Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith NArith.NArith.
Require Import stdpp.bitvector.definitions.
Require Import ZesuSsz.Contracts.ParentHeaderContract.
Require Import ZesuSsz.Contracts.ParentHeaderContract.
Require Import ZesuSsz.Automation2.All.
Local Open Scope Z_scope.
#[local] Typeclasses Transparent parentHeaderSelectedCode.

Definition DesignedEntry_800d61cc_slot1
    `{!islaG Sigma} `{!threadG} (args : ParentHeaderArgs) (returnAddress : Z) (K : iProp Sigma) : iProp Sigma :=
  ((ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot0514Entries.fp_machineAt0514_slot1 (args) (returnAddress) (K)) ∗
   True)%I.
Global Instance : LithiumUnfold (@DesignedEntry_800d61cc_slot1) := I.
Global Typeclasses Opaque DesignedEntry_800d61cc_slot1.

Lemma DesignedBoundary_800d61cc_slot1 `{!islaG Sigma} `{!threadG} (args : ParentHeaderArgs) (returnAddress : Z)  :
  parentHeaderSelectedCode -∗
  instr_body 0x800d61cc
    (DesignedEntry_800d61cc_slot1 args returnAddress (parentHeaderContinuation args returnAddress)).
Proof.
  zesu_block2.
Qed.

Print Assumptions DesignedBoundary_800d61cc_slot1.
