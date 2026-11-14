Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot0168Entries.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot0168Structural.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot00a8Entries.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot00a8Structural.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot0170Entries.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot0170Structural.
Require Import ZesuSsz.Automation2.All.
Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith NArith.NArith.
Require Import stdpp.bitvector.definitions.
Require Import ZesuSsz.Contracts.ParentHeaderContract.
Require Import ZesuSsz.Contracts.ParentHeaderContract.
Require Import ZesuSsz.Automation2.All.
Local Open Scope Z_scope.
#[local] Typeclasses Transparent parentHeaderSelectedCode.

Definition DesignedEntry_800d5e20
    `{!islaG Sigma} `{!threadG} (args : ParentHeaderArgs) (returnAddress : Z) (K : iProp Sigma) : iProp Sigma :=
  ((ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot0168Entries.fp_machineAt0168 (args) (returnAddress) (K)) ∗
   True)%I.
Global Instance : LithiumUnfold (@DesignedEntry_800d5e20) := I.
Global Typeclasses Opaque DesignedEntry_800d5e20.

Lemma DesignedBoundary_800d5e20 `{!islaG Sigma} `{!threadG} (args : ParentHeaderArgs) (returnAddress : Z) (K : iProp Sigma)  :
  instr_pre 0x800d5d60 (ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot00a8Entries.fp_machineAt00a8 (args) (returnAddress) (K))%I -∗
  instr_pre 0x800d5e28 (ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot0170Entries.fp_machineAt0170 (args) (returnAddress) (K))%I -∗
  parentHeaderSelectedCode -∗
  instr_body 0x800d5e20
    (DesignedEntry_800d5e20 args returnAddress K).
Proof.
  zesu_block2.
Qed.

Print Assumptions DesignedBoundary_800d5e20.
