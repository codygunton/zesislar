Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot5dfcEntries.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot5dfcStructural.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot5e18Entries.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot5e18Structural.
Require Import ZesuSsz.Contracts.DecodeItemCallSpec2.
Require Import ZesuSsz.Automation2.All.
Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith NArith.NArith.
Require Import stdpp.bitvector.definitions.
Require Import ZesuSsz.Contracts.ParentHeaderContract.
Require Import ZesuSsz.Contracts.ParentHeaderLookupCode.
Require Import ZesuSsz.Automation2.All.
Local Open Scope Z_scope.

Definition DesignedEntry_800d5dfc
    `{!islaG Sigma} `{!threadG} (args : ParentHeaderArgs) (returnAddress : Z) (K : iProp Sigma) : iProp Sigma :=
  ((ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot5dfcEntries.fp_machineAt5dfc (args) (returnAddress) (K)) ∗
   True)%I.
Global Instance : LithiumUnfold (@DesignedEntry_800d5dfc) := I.
Global Typeclasses Opaque DesignedEntry_800d5dfc.

Lemma DesignedBoundary_800d5dfc `{!islaG Sigma} `{!threadG} (args : ParentHeaderArgs) (returnAddress : Z) (K : iProp Sigma)  :
  instr_pre 0x800d5e18 (ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot5e18Entries.fp_machineAt5e18 (args) (returnAddress) (K))%I -∗
  instr_pre 0x800d6960 (ZesuSsz.Contracts.DecodeItemCallSpec2.decodeItemCallSpec2)%I -∗
  parentHeaderLookupCode -∗
  instr_body 0x800d5dfc
    (DesignedEntry_800d5dfc args returnAddress K).
Proof.
  zesu_block2.
Qed.

Print Assumptions DesignedBoundary_800d5dfc.
