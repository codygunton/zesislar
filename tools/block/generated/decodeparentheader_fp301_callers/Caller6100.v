Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot6100Entries.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot6100Structural.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot611cEntries.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot611cStructural.
Require Import ZesuSsz.Contracts.DecodeItemCallSpec2.
Require Import ZesuSsz.Automation2.All.
Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith NArith.NArith.
Require Import stdpp.bitvector.definitions.
Require Import ZesuSsz.Contracts.ParentHeaderContract.
Require Import ZesuSsz.Contracts.ParentHeaderContract.
Require Import ZesuSsz.Automation2.All.
Local Open Scope Z_scope.
#[local] Typeclasses Transparent parentHeaderSelectedCode.

Definition DesignedEntry_800d6100
    `{!islaG Sigma} `{!threadG} (args : ParentHeaderArgs) (returnAddress : Z) (K : iProp Sigma) : iProp Sigma :=
  ((ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot6100Entries.fp_machineAt6100 (args) (returnAddress) (K)) ∗
   True)%I.
Global Instance : LithiumUnfold (@DesignedEntry_800d6100) := I.
Global Typeclasses Opaque DesignedEntry_800d6100.

Lemma DesignedBoundary_800d6100 `{!islaG Sigma} `{!threadG} (args : ParentHeaderArgs) (returnAddress : Z) (K : iProp Sigma)  :
  instr_pre 0x800d611c (ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot611cEntries.fp_machineAt611c (args) (returnAddress) (K))%I -∗
  instr_pre 0x800d6960 (ZesuSsz.Contracts.DecodeItemCallSpec2.decodeItemCallSpec2)%I -∗
  parentHeaderSelectedCode -∗
  instr_body 0x800d6100
    (DesignedEntry_800d6100 args returnAddress K).
Proof.
  zesu_block2.
Qed.

Print Assumptions DesignedBoundary_800d6100.
