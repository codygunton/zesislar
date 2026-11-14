Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot0314Entries.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot0314Structural.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot026cEntries.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot026cStructural.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot0320Entries.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot0320Structural.
Require Import ZesuSsz.Automation2.All.
Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith NArith.NArith.
Require Import stdpp.bitvector.definitions.
Require Import ZesuSsz.Contracts.ParentHeaderContract.
Require Import ZesuSsz.Contracts.ParentHeaderContract.
Require Import ZesuSsz.Automation2.All.
Local Open Scope Z_scope.
#[local] Typeclasses Transparent parentHeaderSelectedCode.

Definition DesignedEntry_800d5fcc
    `{!islaG Sigma} `{!threadG} (args : ParentHeaderArgs) (returnAddress : Z) (K : iProp Sigma) : iProp Sigma :=
  ((ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot0314Entries.fp_machineAt0314 (args) (returnAddress) (K)) ∗
   True)%I.
Global Instance : LithiumUnfold (@DesignedEntry_800d5fcc) := I.
Global Typeclasses Opaque DesignedEntry_800d5fcc.

Lemma DesignedBoundary_800d5fcc `{!islaG Sigma} `{!threadG} (args : ParentHeaderArgs) (returnAddress : Z) (K : iProp Sigma)  :
  instr_pre 0x800d5f24 (ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot026cEntries.fp_machineAt026c (args) (returnAddress) (K))%I -∗
  instr_pre 0x800d5fd8 (ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot0320Entries.fp_machineAt0320 (args) (returnAddress) (K))%I -∗
  parentHeaderSelectedCode -∗
  instr_body 0x800d5fcc
    (DesignedEntry_800d5fcc args returnAddress K).
Proof.
  zesu_block2.
Qed.

Print Assumptions DesignedBoundary_800d5fcc.
