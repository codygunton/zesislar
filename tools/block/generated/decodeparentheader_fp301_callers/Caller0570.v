Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot0570Entries.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot0570Structural.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot0514Entries.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot0514Structural.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot058cEntries.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot058cStructural.
Require Import ZesuSsz.Automation2.All.
Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith NArith.NArith.
Require Import stdpp.bitvector.definitions.
Require Import ZesuSsz.Contracts.ParentHeaderContract.
Require Import ZesuSsz.Contracts.ParentHeaderContract.
Require Import ZesuSsz.Automation2.All.
Local Open Scope Z_scope.
#[local] Typeclasses Transparent parentHeaderSelectedCode.

Definition DesignedEntry_800d6228
    `{!islaG Sigma} `{!threadG} (args : ParentHeaderArgs) (returnAddress : Z) (K : iProp Sigma) : iProp Sigma :=
  ((ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot0570Entries.fp_machineAt0570 (args) (returnAddress) (K)) ∗
   True)%I.
Global Instance : LithiumUnfold (@DesignedEntry_800d6228) := I.
Global Typeclasses Opaque DesignedEntry_800d6228.

Lemma DesignedBoundary_800d6228 `{!islaG Sigma} `{!threadG} (args : ParentHeaderArgs) (returnAddress : Z) (K : iProp Sigma)  :
  instr_pre 0x800d61cc (ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot0514Entries.fp_machineAt0514_slot0 (args) (returnAddress) (K))%I -∗
  instr_pre 0x800d6244 (ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot058cEntries.fp_machineAt058c (args) (returnAddress) (K))%I -∗
  parentHeaderSelectedCode -∗
  instr_body 0x800d6228
    (DesignedEntry_800d6228 args returnAddress K).
Proof.
  zesu_block2.
Qed.

Print Assumptions DesignedBoundary_800d6228.
