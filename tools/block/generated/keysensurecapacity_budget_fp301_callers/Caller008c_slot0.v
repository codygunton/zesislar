Require Import ZesuSsz.Generated.KeysEnsureCapacityBudget.FP301.Pilot008cEntries.
Require Import ZesuSsz.Generated.KeysEnsureCapacityBudget.FP301.Pilot008cStructural.
Require Import ZesuSsz.Generated.KeysEnsureCapacityBudget.FP301.FunctionReturnEntries.
Require Import ZesuSsz.Generated.KeysEnsureCapacityBudget.FP301.FunctionReturnStructural.
Require Import ZesuSsz.Automation2.StepBudget.
Require Import ZesuSsz.Automation2.All.
Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith NArith.NArith.
Require Import stdpp.bitvector.definitions.
Require Import ZesuSsz.Contracts.KeysEnsureCapacityBlockEntries.
Require Import ZesuSsz.Contracts.KeysEnsureCapacityChargedSelected.
Require Import ZesuSsz.Generated.KeysEnsureCapacityBudget.FP301.Edges008c.
Require Import ZesuSsz.Automation2.All.
Local Open Scope Z_scope.
#[local] Typeclasses Transparent keysEnsureCapacityChargedCode.

Definition DesignedEntry_800cb498_slot0
    `{!islaG Sigma} `{!threadG} (args : KeysEnsureCapacityBlockArgs) (returnAddress : Z) (K : iProp Sigma) : iProp Sigma :=
  ((ZesuSsz.Generated.KeysEnsureCapacityBudget.FP301.Pilot008cEntries.fp_machineAt008c_slot0 (args) (returnAddress) (K)) ∗
   True)%I.
Global Instance : LithiumUnfold (@DesignedEntry_800cb498_slot0) := I.
Global Typeclasses Opaque DesignedEntry_800cb498_slot0.

Lemma DesignedBoundary_800cb498_slot0 `{!islaG Sigma} `{!threadG} (args : KeysEnsureCapacityBlockArgs) (returnAddress : Z) (K : iProp Sigma)  :
  instr_pre returnAddress (ZesuSsz.Generated.KeysEnsureCapacityBudget.FP301.FunctionReturnEntries.fp_machineReturn_slot0 args returnAddress K) -∗
  keysEnsureCapacityChargedCode -∗
  instr_body 0x800cb498
    (DesignedEntry_800cb498_slot0 args returnAddress K).
Proof.
  zesu_block2.
Qed.

Print Assumptions DesignedBoundary_800cb498_slot0.
