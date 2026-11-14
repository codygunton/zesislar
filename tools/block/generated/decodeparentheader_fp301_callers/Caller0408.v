Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot0408Entries.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot0408Structural.
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

Definition DesignedEntry_800d60c0
    `{!islaG Sigma} `{!threadG} (args : ParentHeaderArgs) (returnAddress : Z) (K : iProp Sigma) : iProp Sigma :=
  ((ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot0408Entries.fp_machineAt0408 (args) (returnAddress) (K)) ∗
   True)%I.
Global Instance : LithiumUnfold (@DesignedEntry_800d60c0) := I.
Global Typeclasses Opaque DesignedEntry_800d60c0.

Lemma DesignedBoundary_800d60c0 `{!islaG Sigma} `{!threadG} (args : ParentHeaderArgs) (returnAddress : Z) (K : iProp Sigma)  :
  instr_pre 0x800d5d68 (ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot00b0Entries.fp_machineAt00b0 (args) (returnAddress) (K))%I -∗
  parentHeaderSelectedCode -∗
  instr_body 0x800d60c0
    (DesignedEntry_800d60c0 args returnAddress K).
Proof.
  zesu_block2.
Qed.

Print Assumptions DesignedBoundary_800d60c0.
