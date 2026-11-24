Require Import ZesuSsz.Generated.KeysEnsureCapacityBudget.FP301.Pilot0068Entries.
Require Import ZesuSsz.Generated.KeysEnsureCapacityBudget.FP301.Pilot0068Structural.
Require Import ZesuSsz.Generated.KeysEnsureCapacityBudget.FP301.Pilot0074Entries.
Require Import ZesuSsz.Generated.KeysEnsureCapacityBudget.FP301.Pilot0074Structural.
Require Import ZesuSsz.Generated.KeysEnsureCapacityBudget.FP301.Pilot00c0Entries.
Require Import ZesuSsz.Generated.KeysEnsureCapacityBudget.FP301.Pilot00c0Structural.
Require Import ZesuSsz.Automation2.StepBudget.
Require Import ZesuSsz.Automation2.All.
Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith NArith.NArith.
Require Import stdpp.bitvector.definitions.
Require Import ZesuSsz.Contracts.KeysEnsureCapacityBlockEntries.
Require Import ZesuSsz.Contracts.KeysEnsureCapacityChargedSelected.
Require Import ZesuSsz.Generated.KeysEnsureCapacityBudget.FP301.Edges0068.
Require Import ZesuSsz.Automation2.All.
Local Open Scope Z_scope.
#[local] Typeclasses Transparent keysEnsureCapacityChargedCode.

Definition DesignedEntry_800cb474
    `{!islaG Sigma} `{!threadG} (args : KeysEnsureCapacityBlockArgs) (returnAddress : Z) (K : iProp Sigma) : iProp Sigma :=
  ((ZesuSsz.Generated.KeysEnsureCapacityBudget.FP301.Pilot0068Entries.fp_machineAt0068 (args) (returnAddress) (K)) ∗
   True)%I.
Global Instance : LithiumUnfold (@DesignedEntry_800cb474) := I.
Global Typeclasses Opaque DesignedEntry_800cb474.

Lemma DesignedBoundary_800cb474 `{!islaG Sigma} `{!threadG} (args : KeysEnsureCapacityBlockArgs) (returnAddress : Z) (K : iProp Sigma)  :
  instr_pre 0x800cb480 (ZesuSsz.Generated.KeysEnsureCapacityBudget.FP301.Pilot0074Entries.fp_machineAt0074 (args) (returnAddress) (K))%I -∗
  instr_pre 0x800cb4cc (ZesuSsz.Generated.KeysEnsureCapacityBudget.FP301.Pilot00c0Entries.fp_machineAt00c0 (args) (returnAddress) (K))%I -∗
  keysEnsureCapacityChargedCode -∗
  instr_body 0x800cb474
    (DesignedEntry_800cb474 args returnAddress K).
Proof.
  zesu_block2.
Qed.

Print Assumptions DesignedBoundary_800cb474.
