Require Import ZesuSsz.Generated.DecodeItemBudget.FP301.Pilot001cEntries.
Require Import ZesuSsz.Generated.DecodeItemBudget.FP301.Pilot001cStructural.
Require Import ZesuSsz.Generated.DecodeItemBudget.FP301.Pilot002cEntries.
Require Import ZesuSsz.Generated.DecodeItemBudget.FP301.Pilot002cStructural.
Require Import ZesuSsz.Automation2.StepBudget.
Require Import ZesuSsz.Automation2.All.
Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith NArith.NArith.
Require Import stdpp.bitvector.definitions.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Require Import ZesuSsz.Contracts.DecodeItemChargedSelected.
Require Import ZesuSsz.Automation2.All.
Require Import ZesuSsz.Residuals.Block800d697c.
Local Open Scope Z_scope.
#[local] Typeclasses Transparent decodeItemChargedCode.

Definition DesignedEntry_800d697c
    `{!islaG Sigma} `{!threadG} (args : DecodeItemArgs) (returnAddress : Z) (K : iProp Sigma) : iProp Sigma :=
  ((ZesuSsz.Generated.DecodeItemBudget.FP301.Pilot001cEntries.fp_machineAt001c (args) (returnAddress) (K)) ∗
   True)%I.
Global Instance : LithiumUnfold (@DesignedEntry_800d697c) := I.
Global Typeclasses Opaque DesignedEntry_800d697c.

Lemma DesignedBoundary_800d697c `{!islaG Sigma} `{!threadG} (args : DecodeItemArgs) (returnAddress : Z) (K : iProp Sigma)  :
  instr_pre 0x800d698c (ZesuSsz.Generated.DecodeItemBudget.FP301.Pilot002cEntries.fp_machineAt002c (args) (returnAddress) (K))%I -∗
  decodeItemChargedCode -∗
  instr_body 0x800d697c
    (DesignedEntry_800d697c args returnAddress K).
Proof.
  zesu_block2.
Qed.

Print Assumptions DesignedBoundary_800d697c.
