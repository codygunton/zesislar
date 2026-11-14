Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot5e28Entries.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot5e28Structural.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot5e44Entries.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot5e44Structural.
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

Definition DesignedEntry_800d5e28
    `{!islaG Sigma} `{!threadG} (args : ParentHeaderArgs) (returnAddress : Z) (K : iProp Sigma) : iProp Sigma :=
  ((ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot5e28Entries.fp_machineAt5e28 (args) (returnAddress) (K)) ∗
   True)%I.
Global Instance : LithiumUnfold (@DesignedEntry_800d5e28) := I.
Global Typeclasses Opaque DesignedEntry_800d5e28.

Lemma DesignedBoundary_800d5e28 `{!islaG Sigma} `{!threadG} (args : ParentHeaderArgs) (returnAddress : Z) (K : iProp Sigma)  :
  instr_pre 0x800d5e44 (ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot5e44Entries.fp_machineAt5e44 (args) (returnAddress) (K))%I -∗
  instr_pre 0x800d6960 (ZesuSsz.Contracts.DecodeItemCallSpec2.decodeItemCallSpec2)%I -∗
  parentHeaderSelectedCode -∗
  instr_body 0x800d5e28
    (DesignedEntry_800d5e28 args returnAddress K).
Proof.
  zesu_block2.
Qed.

Print Assumptions DesignedBoundary_800d5e28.
