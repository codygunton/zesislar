Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot0244Entries.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot0244Structural.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot0264Entries.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot0264Structural.
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

Definition DesignedEntry_800d5efc
    `{!islaG Sigma} `{!threadG} (args : ParentHeaderArgs) (returnAddress : Z) (K : iProp Sigma) : iProp Sigma :=
  ((ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot0244Entries.fp_machineAt0244 (args) (returnAddress) (K)) ∗
   True)%I.
Global Instance : LithiumUnfold (@DesignedEntry_800d5efc) := I.
Global Typeclasses Opaque DesignedEntry_800d5efc.

Lemma DesignedBoundary_800d5efc `{!islaG Sigma} `{!threadG} (args : ParentHeaderArgs) (returnAddress : Z) (K : iProp Sigma)  :
  instr_pre 0x800d5f1c (ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot0264Entries.fp_machineAt0264 (args) (returnAddress) (K))%I -∗
  instr_pre 0x800d6960 (ZesuSsz.Contracts.DecodeItemCallSpec2.decodeItemCallSpec2)%I -∗
  parentHeaderSelectedCode -∗
  instr_body 0x800d5efc
    (DesignedEntry_800d5efc args returnAddress K).
Proof.
  zesu_block2.
Qed.

Print Assumptions DesignedBoundary_800d5efc.
