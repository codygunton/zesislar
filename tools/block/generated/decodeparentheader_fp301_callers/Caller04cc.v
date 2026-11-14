Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot04ccEntries.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot04ccStructural.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot04e4Entries.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot04e4Structural.
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

Definition DesignedEntry_800d6184
    `{!islaG Sigma} `{!threadG} (args : ParentHeaderArgs) (returnAddress : Z) (K : iProp Sigma) : iProp Sigma :=
  ((ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot04ccEntries.fp_machineAt04cc (args) (returnAddress) (K)) ∗
   True)%I.
Global Instance : LithiumUnfold (@DesignedEntry_800d6184) := I.
Global Typeclasses Opaque DesignedEntry_800d6184.

Lemma DesignedBoundary_800d6184 `{!islaG Sigma} `{!threadG} (args : ParentHeaderArgs) (returnAddress : Z) (K : iProp Sigma)  :
  instr_pre 0x800d619c (ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot04e4Entries.fp_machineAt04e4 (args) (returnAddress) (K))%I -∗
  instr_pre 0x800d6960 (ZesuSsz.Contracts.DecodeItemCallSpec2.decodeItemCallSpec2)%I -∗
  parentHeaderSelectedCode -∗
  instr_body 0x800d6184
    (DesignedEntry_800d6184 args returnAddress K).
Proof.
  zesu_block2.
Qed.

Print Assumptions DesignedBoundary_800d6184.
