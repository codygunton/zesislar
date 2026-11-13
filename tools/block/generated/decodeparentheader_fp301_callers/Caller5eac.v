Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot5eacEntries.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot5eacStructural.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot5ec8Entries.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot5ec8Structural.
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

Definition DesignedEntry_800d5eac
    `{!islaG Sigma} `{!threadG} (args : ParentHeaderArgs) (returnAddress : Z) (K : iProp Sigma) : iProp Sigma :=
  ((ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot5eacEntries.fp_machineAt5eac (args) (returnAddress) (K)) ∗
   True)%I.
Global Instance : LithiumUnfold (@DesignedEntry_800d5eac) := I.
Global Typeclasses Opaque DesignedEntry_800d5eac.

Lemma DesignedBoundary_800d5eac `{!islaG Sigma} `{!threadG} (args : ParentHeaderArgs) (returnAddress : Z) (K : iProp Sigma)  :
  instr_pre 0x800d5ec8 (ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot5ec8Entries.fp_machineAt5ec8 (args) (returnAddress) (K))%I -∗
  instr_pre 0x800d6960 (ZesuSsz.Contracts.DecodeItemCallSpec2.decodeItemCallSpec2)%I -∗
  parentHeaderSelectedCode -∗
  instr_body 0x800d5eac
    (DesignedEntry_800d5eac args returnAddress K).
Proof.
  zesu_block2.
Qed.

Print Assumptions DesignedBoundary_800d5eac.
