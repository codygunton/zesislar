Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot0080Entries.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot0080Structural.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot0088Entries.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot0088Structural.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot00a0Entries.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot00a0Structural.
Require Import ZesuSsz.Automation2.All.
Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith NArith.NArith.
Require Import stdpp.bitvector.definitions.
Require Import ZesuSsz.Contracts.ParentHeaderContract.
Require Import ZesuSsz.Contracts.ParentHeaderContract.
Require Import ZesuSsz.Automation2.All.
Local Open Scope Z_scope.
#[local] Typeclasses Transparent parentHeaderSelectedCode.

Definition DesignedEntry_800d5d38
    `{!islaG Sigma} `{!threadG} (args : ParentHeaderArgs) (returnAddress : Z) (K : iProp Sigma) : iProp Sigma :=
  ((ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot0080Entries.fp_machineAt0080 (args) (returnAddress) (K)) ∗
   True)%I.
Global Instance : LithiumUnfold (@DesignedEntry_800d5d38) := I.
Global Typeclasses Opaque DesignedEntry_800d5d38.

Lemma DesignedBoundary_800d5d38 `{!islaG Sigma} `{!threadG} (args : ParentHeaderArgs) (returnAddress : Z) (K : iProp Sigma)  :
  instr_pre 0x800d5d40 (ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot0088Entries.fp_machineAt0088 (args) (returnAddress) (K))%I -∗
  instr_pre 0x800d5d58 (ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot00a0Entries.fp_machineAt00a0 (args) (returnAddress) (K))%I -∗
  parentHeaderSelectedCode -∗
  instr_body 0x800d5d38
    (DesignedEntry_800d5d38 args returnAddress K).
Proof.
  zesu_block2.
Qed.

Print Assumptions DesignedBoundary_800d5d38.
