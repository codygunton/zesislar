Require Import ZesuSsz.Generated.DecodeItemBudget.FP301.Pilot0104Entries.
Require Import ZesuSsz.Generated.DecodeItemBudget.FP301.Pilot0104Structural.
Require Import ZesuSsz.Generated.DecodeItemBudget.FP301.Pilot010cEntries.
Require Import ZesuSsz.Generated.DecodeItemBudget.FP301.Pilot010cStructural.
Require Import ZesuSsz.Generated.DecodeItemBudget.FP301.Pilot0148Entries.
Require Import ZesuSsz.Generated.DecodeItemBudget.FP301.Pilot0148Structural.
Require Import ZesuSsz.Automation2.StepBudget.
Require Import ZesuSsz.Automation2.All.
Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith NArith.NArith.
Require Import stdpp.bitvector.definitions.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Require Import ZesuSsz.Contracts.DecodeItemChargedSelected.
Require Import ZesuSsz.Automation2.All.
Local Open Scope Z_scope.
#[local] Typeclasses Transparent decodeItemChargedCode.

Definition DesignedEntry_800d6a64
    `{!islaG Sigma} `{!threadG} (args : DecodeItemArgs) (returnAddress : Z) (K : iProp Sigma) : iProp Sigma :=
  ((ZesuSsz.Generated.DecodeItemBudget.FP301.Pilot0104Entries.fp_machineAt0104 (args) (returnAddress) (K)) ∗
   True)%I.
Global Instance : LithiumUnfold (@DesignedEntry_800d6a64) := I.
Global Typeclasses Opaque DesignedEntry_800d6a64.

Lemma DesignedBoundary_800d6a64 `{!islaG Sigma} `{!threadG} (args : DecodeItemArgs) (returnAddress : Z) (K : iProp Sigma)  :
  instr_pre 0x800d6a6c (ZesuSsz.Generated.DecodeItemBudget.FP301.Pilot010cEntries.fp_machineAt010c (args) (returnAddress) (K))%I -∗
  instr_pre 0x800d6aa8 (ZesuSsz.Generated.DecodeItemBudget.FP301.Pilot0148Entries.fp_machineAt0148 (args) (returnAddress) (K))%I -∗
  decodeItemChargedCode -∗
  instr_body 0x800d6a64
    (DesignedEntry_800d6a64 args returnAddress K).
Proof.
  zesu_block2.
Qed.

Print Assumptions DesignedBoundary_800d6a64.
