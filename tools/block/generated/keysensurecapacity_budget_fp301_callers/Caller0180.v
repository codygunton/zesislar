Require Import ZesuSsz.Generated.KeysEnsureCapacityBudget.FP301.Pilot0180Entries.
Require Import ZesuSsz.Generated.KeysEnsureCapacityBudget.FP301.Pilot0180Structural.
Require Import ZesuSsz.Generated.KeysEnsureCapacityBudget.FP301.Pilot019cEntries.
Require Import ZesuSsz.Generated.KeysEnsureCapacityBudget.FP301.Pilot019cStructural.
Require Import ZesuSsz.Contracts.AltFlAllocPremises.
Require Import ZesuSsz.Automation2.StepBudget.
Require Import ZesuSsz.Automation2.All.
Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith NArith.NArith.
Require Import stdpp.bitvector.definitions.
Require Import ZesuSsz.Contracts.KeysEnsureCapacityBlockEntries.
Require Import ZesuSsz.Contracts.KeysEnsureCapacityChargedSelected.
Require Import ZesuSsz.Generated.KeysEnsureCapacityBudget.FP301.Edges0180.
Require Import ZesuSsz.Automation2.All.
Local Open Scope Z_scope.
#[local] Typeclasses Transparent keysEnsureCapacityChargedCode.

Definition DesignedEntry_800cb58c
    `{!islaG Sigma} `{!threadG} (args : KeysEnsureCapacityBlockArgs) (returnAddress : Z) (K : iProp Sigma) : iProp Sigma :=
  ((ZesuSsz.Generated.KeysEnsureCapacityBudget.FP301.Pilot0180Entries.fp_machineAt0180 (args) (returnAddress) (K)) ∗
   True)%I.
Global Instance : LithiumUnfold (@DesignedEntry_800cb58c) := I.
Global Typeclasses Opaque DesignedEntry_800cb58c.

Lemma DesignedBoundary_800cb58c `{!islaG Sigma} `{!threadG} (args : KeysEnsureCapacityBlockArgs) (returnAddress : Z) (K : iProp Sigma)  :
  instr_pre 0x800cb5a8 (ZesuSsz.Generated.KeysEnsureCapacityBudget.FP301.Pilot019cEntries.fp_machineAt019c (args) (returnAddress) (K))%I -∗
  instr_pre 0x80041f38 (step_budget (42) ∗ ZesuSsz.Contracts.AltFlAllocPremises.altFlFreeCallSpec)%I -∗
  keysEnsureCapacityChargedCode -∗
  instr_body 0x800cb58c
    (DesignedEntry_800cb58c args returnAddress K).
Proof.
  zesu_block2.
Qed.

Print Assumptions DesignedBoundary_800cb58c.
