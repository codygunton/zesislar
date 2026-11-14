Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot04f8Entries.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot04f8Structural.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot0510Entries.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot0510Structural.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot0558Entries.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot0558Structural.
Require Import ZesuSsz.Automation2.All.
Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith NArith.NArith.
Require Import stdpp.bitvector.definitions.
Require Import ZesuSsz.Contracts.ParentHeaderContract.
Require Import ZesuSsz.Contracts.ParentHeaderContract.
Require Import ZesuSsz.Automation2.All.
Local Open Scope Z_scope.
#[local] Typeclasses Transparent parentHeaderSelectedCode.

Definition DesignedEntry_800d61b0
    `{!islaG Sigma} `{!threadG} (args : ParentHeaderArgs) (returnAddress : Z) (K : iProp Sigma) : iProp Sigma :=
  ((ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot04f8Entries.fp_machineAt04f8 (args) (returnAddress) (K)) ∗
   True)%I.
Global Instance : LithiumUnfold (@DesignedEntry_800d61b0) := I.
Global Typeclasses Opaque DesignedEntry_800d61b0.

Lemma DesignedBoundary_800d61b0 `{!islaG Sigma} `{!threadG} (args : ParentHeaderArgs) (returnAddress : Z) (K : iProp Sigma)  :
  instr_pre 0x800d61c8 (ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot0510Entries.fp_machineAt0510_slot1 (args) (returnAddress) (K))%I -∗
  instr_pre 0x800d6210 (ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot0558Entries.fp_machineAt0558 (args) (returnAddress) (K))%I -∗
  parentHeaderSelectedCode -∗
  instr_body 0x800d61b0
    (DesignedEntry_800d61b0 args returnAddress K).
Proof.
  zesu_block2.
Qed.

Print Assumptions DesignedBoundary_800d61b0.
