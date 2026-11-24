Require Import ZesuSsz.Generated.DecodeItemBudget.FP301.Pilot0050Entries.
Require Import ZesuSsz.Generated.DecodeItemBudget.FP301.Pilot0050Structural.
Require Import ZesuSsz.Generated.DecodeItemBudget.FP301.FunctionReturnEntries.
Require Import ZesuSsz.Generated.DecodeItemBudget.FP301.FunctionReturnStructural.
Require Import ZesuSsz.Automation2.StepBudget.
Require Import ZesuSsz.Automation2.All.
Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith NArith.NArith.
Require Import stdpp.bitvector.definitions.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Require Import ZesuSsz.Contracts.DecodeItemChargedSelected.
Require Import ZesuSsz.Automation2.All.
Require Import ZesuSsz.Compliance.DecodeItemMeaningPorted.
Require Import ZesuSsz.Residuals.Block800d69b0.
Local Open Scope Z_scope.
#[local] Typeclasses Transparent decodeItemChargedCode.

Definition DesignedEntry_800d69b0
    `{!islaG Sigma} `{!threadG} (args : DecodeItemArgs) (returnAddress : Z) (K : iProp Sigma) : iProp Sigma :=
  ((ZesuSsz.Generated.DecodeItemBudget.FP301.Pilot0050Entries.fp_machineAt0050 (args) (returnAddress) (K)) ∗
   True)%I.
Global Instance : LithiumUnfold (@DesignedEntry_800d69b0) := I.
Global Typeclasses Opaque DesignedEntry_800d69b0.

Lemma DesignedBoundary_800d69b0 `{!islaG Sigma} `{!threadG} (args : DecodeItemArgs) (returnAddress : Z) (K : iProp Sigma)  :
  instr_pre returnAddress (ZesuSsz.Generated.DecodeItemBudget.FP301.FunctionReturnEntries.fp_machineReturn args returnAddress K) -∗
  decodeItemChargedCode -∗
  instr_body 0x800d69b0
    (DesignedEntry_800d69b0 args returnAddress K).
Proof.
  zesu_block2.
Qed.

Print Assumptions DesignedBoundary_800d69b0.
