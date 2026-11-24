Require Import ZesuSsz.Generated.KeysEnsureCapacityBudget.FP301.Pilot0104Entries.
Require Import ZesuSsz.Generated.KeysEnsureCapacityBudget.FP301.Pilot0104Structural.
Require Import ZesuSsz.Generated.KeysEnsureCapacityBudget.FP301.Pilot0118Entries.
Require Import ZesuSsz.Generated.KeysEnsureCapacityBudget.FP301.Pilot0118Structural.
Require Import ZesuSsz.Automation2.StepBudget.
Require Import ZesuSsz.Automation2.All.
Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith NArith.NArith.
Require Import stdpp.bitvector.definitions.
Require Import ZesuSsz.Contracts.KeysEnsureCapacityBlockEntries.
Require Import ZesuSsz.Contracts.KeysEnsureCapacityChargedSelected.
Require Import ZesuSsz.Automation2.All.
Local Open Scope Z_scope.
#[local] Typeclasses Transparent keysEnsureCapacityChargedCode.

Definition DesignedEntry_800cb510
    `{!islaG Sigma} `{!threadG} (args : KeysEnsureCapacityBlockArgs) (returnAddress : Z) (K : iProp Sigma) : iProp Sigma :=
  ((ZesuSsz.Generated.KeysEnsureCapacityBudget.FP301.Pilot0104Entries.fp_machineAt0104 (args) (returnAddress) (K)) ∗
   True)%I.
Global Instance : LithiumUnfold (@DesignedEntry_800cb510) := I.
Global Typeclasses Opaque DesignedEntry_800cb510.

Lemma DesignedBoundary_800cb510 `{!islaG Sigma} `{!threadG} (args : KeysEnsureCapacityBlockArgs) (returnAddress : Z) (K : iProp Sigma)  :
  instr_pre 0x800cb524 (ZesuSsz.Generated.KeysEnsureCapacityBudget.FP301.Pilot0118Entries.fp_machineAt0118 (args) (returnAddress) (K))%I -∗
  keysEnsureCapacityChargedCode -∗
  instr_body 0x800cb510
    (DesignedEntry_800cb510 args returnAddress K).
Proof.
  zesu_block2.
Qed.

Print Assumptions DesignedBoundary_800cb510.
