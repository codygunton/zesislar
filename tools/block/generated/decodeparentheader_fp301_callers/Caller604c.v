Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot604cEntries.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot604cStructural.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot6054Entries.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot6054Structural.
Require Import ZesuSsz.Automation2.All.
Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith NArith.NArith.
Require Import stdpp.bitvector.definitions.
Require Import ZesuSsz.Contracts.ParentHeaderContract.
Require Import ZesuSsz.Contracts.ParentHeaderContract.
Require Import ZesuSsz.Automation2.All.
Local Open Scope Z_scope.
#[local] Typeclasses Transparent parentHeaderSelectedCode.

Definition DesignedEntry_800d604c
    `{!islaG Sigma} `{!threadG} (args : ParentHeaderArgs) (returnAddress : Z) (K : iProp Sigma) : iProp Sigma :=
  ((ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot604cEntries.fp_machineAt604c (args) (returnAddress) (K)) ∗
   True)%I.
Global Instance : LithiumUnfold (@DesignedEntry_800d604c) := I.
Global Typeclasses Opaque DesignedEntry_800d604c.

Lemma DesignedBoundary_800d604c `{!islaG Sigma} `{!threadG} (args : ParentHeaderArgs) (returnAddress : Z) (K : iProp Sigma)  :
  instr_pre 0x800d6054 (ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot6054Entries.fp_machineAt6054 (args) (returnAddress) (K))%I -∗
  parentHeaderSelectedCode -∗
  instr_body 0x800d604c
    (DesignedEntry_800d604c args returnAddress K).
Proof.
  zesu_block2.
Qed.

Print Assumptions DesignedBoundary_800d604c.
