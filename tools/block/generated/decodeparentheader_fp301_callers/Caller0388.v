Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot0388Entries.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot0388Structural.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot0394Entries.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot0394Structural.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot03b0Entries.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot03b0Structural.
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
  ((ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot0388Entries.fp_machineAt0388 (args) (returnAddress) (K)) ∗
   True)%I.
Global Instance : LithiumUnfold (@DesignedEntry_800d6040) := I.
Global Typeclasses Opaque DesignedEntry_800d6040.

Lemma DesignedBoundary_800d6040 `{!islaG Sigma} `{!threadG} (args : ParentHeaderArgs) (returnAddress : Z) (K : iProp Sigma)  :
  instr_pre 0x800d604c (ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot0394Entries.fp_machineAt0394 (args) (returnAddress) (K))%I -∗
  instr_pre 0x800d6068 (ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot03b0Entries.fp_machineAt03b0 (args) (returnAddress) (K))%I -∗
  parentHeaderSelectedCode -∗
  instr_body 0x800d6040
    (DesignedEntry_800d6040 args returnAddress K).
Proof.
  zesu_block2.
Qed.

Print Assumptions DesignedBoundary_800d6040.
