Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot5fe4Entries.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot5fe4Structural.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot5fecEntries.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot5fecStructural.
Require Import ZesuSsz.Automation2.All.
Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith NArith.NArith.
Require Import stdpp.bitvector.definitions.
Require Import ZesuSsz.Contracts.ParentHeaderContract.
Require Import ZesuSsz.Contracts.ParentHeaderContract.
Require Import ZesuSsz.Automation2.All.
Local Open Scope Z_scope.
#[local] Typeclasses Transparent parentHeaderSelectedCode.

Definition DesignedEntry_800d5fe4
    `{!islaG Sigma} `{!threadG} (args : ParentHeaderArgs) (returnAddress : Z) (K : iProp Sigma) : iProp Sigma :=
  ((ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot5fe4Entries.fp_machineAt5fe4 (args) (returnAddress) (K)) ∗
   True)%I.
Global Instance : LithiumUnfold (@DesignedEntry_800d5fe4) := I.
Global Typeclasses Opaque DesignedEntry_800d5fe4.

Lemma DesignedBoundary_800d5fe4 `{!islaG Sigma} `{!threadG} (args : ParentHeaderArgs) (returnAddress : Z) (K : iProp Sigma)  :
  instr_pre 0x800d5fec (ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot5fecEntries.fp_machineAt5fec (args) (returnAddress) (K))%I -∗
  parentHeaderSelectedCode -∗
  instr_body 0x800d5fe4
    (DesignedEntry_800d5fe4 args returnAddress K).
Proof.
  zesu_block2.
Qed.

Print Assumptions DesignedBoundary_800d5fe4.
