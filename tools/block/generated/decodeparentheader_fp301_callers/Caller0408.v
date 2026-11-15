Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot0408Entries.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot0408Structural.
Require Import ZesuSsz.Compliance.ParentHeaderCompositionBoundary.
Require Import ZesuSsz.Contracts.ParentHeaderMemcpyService.
Require Import ZesuSsz.Automation2.All.
Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith NArith.NArith.
Require Import stdpp.bitvector.definitions.
Require Import ZesuSsz.Contracts.ParentHeaderContract.
Require Import ZesuSsz.Contracts.ParentHeaderContract.
Require Import ZesuSsz.Automation2.All.
Local Open Scope Z_scope.
#[local] Typeclasses Transparent parentHeaderSelectedCode.

Definition DesignedEntry_800d60c0
    `{!islaG Sigma} `{!threadG} (args : ParentHeaderArgs) (returnAddress : Z) (K : iProp Sigma) : iProp Sigma :=
  ((ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot0408Entries.fp_machineAt0408 (args) (returnAddress) (K)) ∗
   True)%I.
Global Instance : LithiumUnfold (@DesignedEntry_800d60c0) := I.
Global Typeclasses Opaque DesignedEntry_800d60c0.

Lemma DesignedBoundary_800d60c0 `{!islaG Sigma} `{!threadG} (args : ParentHeaderArgs) (returnAddress : Z)  :
  instr_pre 0x800e06c0 (ZesuSsz.Contracts.ParentHeaderMemcpyService.memcpyCallSpec2)%I -∗
  parentHeaderSelectedCode -∗
  instr_body 0x800d60c0
    (DesignedEntry_800d60c0 args returnAddress (parentHeaderContinuation args returnAddress)).
Proof.
  zesu_block2.
Qed.

Print Assumptions DesignedBoundary_800d60c0.
