Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot00b0Entries.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot00b0Structural.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.FunctionReturnTail00e8Entries.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.FunctionReturnTail00e8Structural.
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

Definition DesignedEntry_800d5d68
    `{!islaG Sigma} `{!threadG} (args : ParentHeaderArgs) (returnAddress : Z) (K : iProp Sigma) : iProp Sigma :=
  ((ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot00b0Entries.fp_machineAt00b0 (args) (returnAddress) (K)) ∗
   True)%I.
Global Instance : LithiumUnfold (@DesignedEntry_800d5d68) := I.
Global Typeclasses Opaque DesignedEntry_800d5d68.

Lemma DesignedBoundary_800d5d68 `{!islaG Sigma} `{!threadG} (args : ParentHeaderArgs) (returnAddress : Z) (K : iProp Sigma)  :
  instr_pre returnAddress (ZesuSsz.Generated.DecodeParentHeader.FP301.FunctionReturnTail00e8Entries.fp_machineReturnTail00e8 args returnAddress K) -∗
  instr_pre 0x800e06c0 (ZesuSsz.Contracts.ParentHeaderMemcpyService.memcpyCallSpec2)%I -∗
  parentHeaderSelectedCode -∗
  instr_body 0x800d5d68
    (DesignedEntry_800d5d68 args returnAddress K).
Proof.
  zesu_block2.
Qed.

Print Assumptions DesignedBoundary_800d5d68.
