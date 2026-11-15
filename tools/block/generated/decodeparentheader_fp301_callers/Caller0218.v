Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot0218Entries.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot0218Structural.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot00a8Entries.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot00a8Structural.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot0220Entries.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot0220Structural.
Require Import ZesuSsz.Automation2.All.
Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith NArith.NArith.
Require Import stdpp.bitvector.definitions.
Require Import ZesuSsz.Contracts.ParentHeaderContract.
Require Import ZesuSsz.Contracts.ParentHeaderContract.
Require Import ZesuSsz.Automation2.All.
Local Open Scope Z_scope.
#[local] Typeclasses Transparent parentHeaderSelectedCode.

Definition DesignedEntry_800d5ed0
    `{!islaG Sigma} `{!threadG} (args : ParentHeaderArgs) (returnAddress : Z) (K : iProp Sigma) : iProp Sigma :=
  ((ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot0218Entries.fp_machineAt0218 (args) (returnAddress) (K)) ∗
   True)%I.
Global Instance : LithiumUnfold (@DesignedEntry_800d5ed0) := I.
Global Typeclasses Opaque DesignedEntry_800d5ed0.

Lemma DesignedBoundary_800d5ed0 `{!islaG Sigma} `{!threadG} (args : ParentHeaderArgs) (returnAddress : Z) (K : iProp Sigma)  :
  instr_pre 0x800d5d60 (ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot00a8Entries.fp_machineAt00a8 (args) (returnAddress) (K))%I -∗
  instr_pre 0x800d5ed8 (ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot0220Entries.fp_machineAt0220 (args) (returnAddress) (K))%I -∗
  parentHeaderSelectedCode -∗
  instr_body 0x800d5ed0
    (DesignedEntry_800d5ed0 args returnAddress K).
Proof.
  zesu_block2.
Qed.

Print Assumptions DesignedBoundary_800d5ed0.
