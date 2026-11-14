Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot04e4Entries.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot04e4Structural.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot04ecEntries.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot04ecStructural.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot04f8Entries.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot04f8Structural.
Require Import ZesuSsz.Automation2.All.
Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith NArith.NArith.
Require Import stdpp.bitvector.definitions.
Require Import ZesuSsz.Contracts.ParentHeaderContract.
Require Import ZesuSsz.Contracts.ParentHeaderContract.
Require Import ZesuSsz.Automation2.All.
Local Open Scope Z_scope.
#[local] Typeclasses Transparent parentHeaderSelectedCode.

Definition DesignedEntry_800d619c
    `{!islaG Sigma} `{!threadG} (args : ParentHeaderArgs) (returnAddress : Z) (K : iProp Sigma) : iProp Sigma :=
  ((ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot04e4Entries.fp_machineAt04e4 (args) (returnAddress) (K)) ∗
   True)%I.
Global Instance : LithiumUnfold (@DesignedEntry_800d619c) := I.
Global Typeclasses Opaque DesignedEntry_800d619c.

Lemma DesignedBoundary_800d619c `{!islaG Sigma} `{!threadG} (args : ParentHeaderArgs) (returnAddress : Z) (K : iProp Sigma)  :
  instr_pre 0x800d61a4 (ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot04ecEntries.fp_machineAt04ec (args) (returnAddress) (K))%I -∗
  instr_pre 0x800d61b0 (ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot04f8Entries.fp_machineAt04f8 (args) (returnAddress) (K))%I -∗
  parentHeaderSelectedCode -∗
  instr_body 0x800d619c
    (DesignedEntry_800d619c args returnAddress K).
Proof.
  zesu_block2.
Qed.

Print Assumptions DesignedBoundary_800d619c.
