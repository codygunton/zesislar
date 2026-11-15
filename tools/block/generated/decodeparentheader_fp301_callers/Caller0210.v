Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot0210Entries.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot0210Structural.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot0088Entries.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot0088Structural.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot0218Entries.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot0218Structural.
Require Import ZesuSsz.Automation2.All.
Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith NArith.NArith.
Require Import stdpp.bitvector.definitions.
Require Import ZesuSsz.Contracts.ParentHeaderContract.
Require Import ZesuSsz.Contracts.ParentHeaderContract.
Require Import ZesuSsz.Automation2.All.
Local Open Scope Z_scope.
#[local] Typeclasses Transparent parentHeaderSelectedCode.

Definition DesignedEntry_800d5ec8
    `{!islaG Sigma} `{!threadG} (args : ParentHeaderArgs) (returnAddress : Z) (K : iProp Sigma) : iProp Sigma :=
  ((ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot0210Entries.fp_machineAt0210 (args) (returnAddress) (K)) ∗
   True)%I.
Global Instance : LithiumUnfold (@DesignedEntry_800d5ec8) := I.
Global Typeclasses Opaque DesignedEntry_800d5ec8.

Lemma DesignedBoundary_800d5ec8 `{!islaG Sigma} `{!threadG} (args : ParentHeaderArgs) (returnAddress : Z) (K : iProp Sigma)  :
  instr_pre 0x800d5d40 (ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot0088Entries.fp_machineAt0088 (args) (returnAddress) (K))%I -∗
  instr_pre 0x800d5ed0 (ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot0218Entries.fp_machineAt0218 (args) (returnAddress) (K))%I -∗
  parentHeaderSelectedCode -∗
  instr_body 0x800d5ec8
    (DesignedEntry_800d5ec8 args returnAddress K).
Proof.
  zesu_block2.
Qed.

Print Assumptions DesignedBoundary_800d5ec8.
