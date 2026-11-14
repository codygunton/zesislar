Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot0274Entries.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot0274Structural.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.FunctionReturnEntries.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.FunctionReturnStructural.
Require Import ZesuSsz.Automation2.All.
Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith NArith.NArith.
Require Import stdpp.bitvector.definitions.
Require Import ZesuSsz.Contracts.ParentHeaderContract.
Require Import ZesuSsz.Contracts.ParentHeaderContract.
Require Import ZesuSsz.Automation2.All.
Local Open Scope Z_scope.
#[local] Typeclasses Transparent parentHeaderSelectedCode.

Definition DesignedEntry_800d5f2c
    `{!islaG Sigma} `{!threadG} (args : ParentHeaderArgs) (returnAddress : Z) (K : iProp Sigma) : iProp Sigma :=
  ((ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot0274Entries.fp_machineAt0274 (args) (returnAddress) (K)) ∗
   True)%I.
Global Instance : LithiumUnfold (@DesignedEntry_800d5f2c) := I.
Global Typeclasses Opaque DesignedEntry_800d5f2c.

Lemma DesignedBoundary_800d5f2c `{!islaG Sigma} `{!threadG} (args : ParentHeaderArgs) (returnAddress : Z) (K : iProp Sigma)  :
  instr_pre returnAddress (ZesuSsz.Generated.DecodeParentHeader.FP301.FunctionReturnEntries.fp_machineReturn args returnAddress K) -∗
  parentHeaderSelectedCode -∗
  instr_body 0x800d5f2c
    (DesignedEntry_800d5f2c args returnAddress K).
Proof.
  zesu_block2.
Qed.

Print Assumptions DesignedBoundary_800d5f2c.
