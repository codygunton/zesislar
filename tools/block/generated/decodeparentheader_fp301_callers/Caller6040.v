Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot6040Entries.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot6040Structural.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot604cEntries.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot604cStructural.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot6068Entries.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot6068Structural.
Require Import ZesuSsz.Automation2.All.
Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith NArith.NArith.
Require Import stdpp.bitvector.definitions.
Require Import ZesuSsz.Contracts.ParentHeaderContract.
Require Import ZesuSsz.Contracts.ParentHeaderContract.
Require Import ZesuSsz.Automation2.All.
Local Open Scope Z_scope.
#[local] Typeclasses Transparent parentHeaderSelectedCode.

Definition DesignedEntry_800d6040
    `{!islaG Sigma} `{!threadG} (args : ParentHeaderArgs) (returnAddress : Z) (K : iProp Sigma) : iProp Sigma :=
  ((ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot6040Entries.fp_machineAt6040 (args) (returnAddress) (K)) ∗
   True)%I.
Global Instance : LithiumUnfold (@DesignedEntry_800d6040) := I.
Global Typeclasses Opaque DesignedEntry_800d6040.

Lemma DesignedBoundary_800d6040 `{!islaG Sigma} `{!threadG} (args : ParentHeaderArgs) (returnAddress : Z) (K : iProp Sigma)  :
  instr_pre 0x800d604c (ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot604cEntries.fp_machineAt604c (args) (returnAddress) (K))%I -∗
  instr_pre 0x800d6068 (ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot6068Entries.fp_machineAt6068 (args) (returnAddress) (K))%I -∗
  parentHeaderSelectedCode -∗
  instr_body 0x800d6040
    (DesignedEntry_800d6040 args returnAddress K).
Proof.
  zesu_block2.
Qed.

Print Assumptions DesignedBoundary_800d6040.
