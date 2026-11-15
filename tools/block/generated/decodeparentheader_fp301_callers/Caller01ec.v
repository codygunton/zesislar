Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot01ecEntries.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot01ecStructural.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot00a8Entries.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot00a8Structural.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot01f4Entries.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot01f4Structural.
Require Import ZesuSsz.Automation2.All.
Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith NArith.NArith.
Require Import stdpp.bitvector.definitions.
Require Import ZesuSsz.Contracts.ParentHeaderContract.
Require Import ZesuSsz.Contracts.ParentHeaderContract.
Require Import ZesuSsz.Automation2.All.
Local Open Scope Z_scope.
#[local] Typeclasses Transparent parentHeaderSelectedCode.

Definition DesignedEntry_800d5ea4
    `{!islaG Sigma} `{!threadG} (args : ParentHeaderArgs) (returnAddress : Z) (K : iProp Sigma) : iProp Sigma :=
  ((ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot01ecEntries.fp_machineAt01ec (args) (returnAddress) (K)) ∗
   True)%I.
Global Instance : LithiumUnfold (@DesignedEntry_800d5ea4) := I.
Global Typeclasses Opaque DesignedEntry_800d5ea4.

Lemma DesignedBoundary_800d5ea4 `{!islaG Sigma} `{!threadG} (args : ParentHeaderArgs) (returnAddress : Z) (K : iProp Sigma)  :
  instr_pre 0x800d5d60 (ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot00a8Entries.fp_machineAt00a8 (args) (returnAddress) (K))%I -∗
  instr_pre 0x800d5eac (ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot01f4Entries.fp_machineAt01f4 (args) (returnAddress) (K))%I -∗
  parentHeaderSelectedCode -∗
  instr_body 0x800d5ea4
    (DesignedEntry_800d5ea4 args returnAddress K).
Proof.
  zesu_block2.
Qed.

Print Assumptions DesignedBoundary_800d5ea4.
