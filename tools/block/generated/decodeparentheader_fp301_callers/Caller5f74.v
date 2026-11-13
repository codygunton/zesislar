Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot5f74Entries.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot5f74Structural.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot5f80Entries.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot5f80Structural.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot5f9cEntries.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot5f9cStructural.
Require Import ZesuSsz.Automation2.All.
Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith NArith.NArith.
Require Import stdpp.bitvector.definitions.
Require Import ZesuSsz.Contracts.ParentHeaderContract.
Require Import ZesuSsz.Contracts.ParentHeaderLookupCode.
Require Import ZesuSsz.Automation2.All.
Local Open Scope Z_scope.

Definition DesignedEntry_800d5f74
    `{!islaG Sigma} `{!threadG} (args : ParentHeaderArgs) (returnAddress : Z) (K : iProp Sigma) : iProp Sigma :=
  ((ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot5f74Entries.fp_machineAt5f74 (args) (returnAddress) (K)) ∗
   True)%I.
Global Instance : LithiumUnfold (@DesignedEntry_800d5f74) := I.
Global Typeclasses Opaque DesignedEntry_800d5f74.

Lemma DesignedBoundary_800d5f74 `{!islaG Sigma} `{!threadG} (args : ParentHeaderArgs) (returnAddress : Z) (K : iProp Sigma)  :
  instr_pre 0x800d5f80 (ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot5f80Entries.fp_machineAt5f80 (args) (returnAddress) (K))%I -∗
  instr_pre 0x800d5f9c (ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot5f9cEntries.fp_machineAt5f9c (args) (returnAddress) (K))%I -∗
  parentHeaderLookupCode -∗
  instr_body 0x800d5f74
    (DesignedEntry_800d5f74 args returnAddress K).
Proof.
  zesu_block2.
Qed.

Print Assumptions DesignedBoundary_800d5f74.
