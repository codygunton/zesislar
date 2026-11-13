Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot5f80Entries.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot5f80Structural.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot5f88Entries.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot5f88Structural.
Require Import ZesuSsz.Automation2.All.
Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith NArith.NArith.
Require Import stdpp.bitvector.definitions.
Require Import ZesuSsz.Contracts.ParentHeaderContract.
Require Import ZesuSsz.Contracts.ParentHeaderContract.
Require Import ZesuSsz.Automation2.All.
Local Open Scope Z_scope.
#[local] Typeclasses Transparent parentHeaderSelectedCode.

Definition DesignedEntry_800d5f80
    `{!islaG Sigma} `{!threadG} (args : ParentHeaderArgs) (returnAddress : Z) (K : iProp Sigma) : iProp Sigma :=
  ((ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot5f80Entries.fp_machineAt5f80 (args) (returnAddress) (K)) ∗
   True)%I.
Global Instance : LithiumUnfold (@DesignedEntry_800d5f80) := I.
Global Typeclasses Opaque DesignedEntry_800d5f80.

Lemma DesignedBoundary_800d5f80 `{!islaG Sigma} `{!threadG} (args : ParentHeaderArgs) (returnAddress : Z) (K : iProp Sigma)  :
  instr_pre 0x800d5f88 (ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot5f88Entries.fp_machineAt5f88 (args) (returnAddress) (K))%I -∗
  parentHeaderSelectedCode -∗
  instr_body 0x800d5f80
    (DesignedEntry_800d5f80 args returnAddress K).
Proof.
  zesu_block2.
Qed.

Print Assumptions DesignedBoundary_800d5f80.
