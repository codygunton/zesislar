Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot6020Entries.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot6020Structural.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot5f24Entries.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot5f24Structural.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot6028Entries.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot6028Structural.
Require Import ZesuSsz.Automation2.All.
Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith NArith.NArith.
Require Import stdpp.bitvector.definitions.
Require Import ZesuSsz.Contracts.ParentHeaderContract.
Require Import ZesuSsz.Contracts.ParentHeaderContract.
Require Import ZesuSsz.Automation2.All.
Local Open Scope Z_scope.
#[local] Typeclasses Transparent parentHeaderSelectedCode.

Definition DesignedEntry_800d6020
    `{!islaG Sigma} `{!threadG} (args : ParentHeaderArgs) (returnAddress : Z) (K : iProp Sigma) : iProp Sigma :=
  ((ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot6020Entries.fp_machineAt6020 (args) (returnAddress) (K)) ∗
   True)%I.
Global Instance : LithiumUnfold (@DesignedEntry_800d6020) := I.
Global Typeclasses Opaque DesignedEntry_800d6020.

Lemma DesignedBoundary_800d6020 `{!islaG Sigma} `{!threadG} (args : ParentHeaderArgs) (returnAddress : Z) (K : iProp Sigma)  :
  instr_pre 0x800d5f24 (ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot5f24Entries.fp_machineAt5f24 (args) (returnAddress) (K))%I -∗
  instr_pre 0x800d6028 (ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot6028Entries.fp_machineAt6028 (args) (returnAddress) (K))%I -∗
  parentHeaderSelectedCode -∗
  instr_body 0x800d6020
    (DesignedEntry_800d6020 args returnAddress K).
Proof.
  zesu_block2.
Qed.

Print Assumptions DesignedBoundary_800d6020.
